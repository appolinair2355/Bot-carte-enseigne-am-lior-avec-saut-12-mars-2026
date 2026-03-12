import os
import asyncio
import re
import logging
import sys
import random
from dataclasses import dataclass, field
from typing import List, Optional, Dict, Set, Tuple
from datetime import datetime, timedelta
from telethon import TelegramClient, events, utils
from telethon.sessions import StringSession
from telethon.errors import ChatWriteForbiddenError, UserBannedInChannelError
from aiohttp import web
from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas
import io

from config import (
    API_ID, API_HASH, BOT_TOKEN, ADMIN_ID,
    SOURCE_CHANNEL_ID, PREDICTION_CHANNEL_ID, PORT,
    ALL_SUITS, SUIT_DISPLAY
)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[logging.StreamHandler(sys.stdout)]
)
logger = logging.getLogger(__name__)

if not API_ID or API_ID == 0: 
    logger.error("API_ID manquant")
    exit(1)
if not API_HASH: 
    logger.error("API_HASH manquant")
    exit(1)
if not BOT_TOKEN: 
    logger.error("BOT_TOKEN manquant")
    exit(1)

# ============================================================================
# VARIABLES GLOBALES
# ============================================================================

pending_predictions: Dict[int, dict] = {}
current_game_number = 0
last_source_game_number = 0
last_prediction_time: Optional[datetime] = None
prediction_channel_ok = False
client = None
suit_block_until: Dict[str, datetime] = {}
waiting_finalization: Dict[int, dict] = {}

# Compteur2 - Gestion des costumes manquants (interne uniquement)
compteur2_trackers: Dict[str, 'Compteur2Tracker'] = {}
compteur2_seuil_B = 2  # Seuil par défaut global
compteur2_seuil_by_suit: Dict[str, int] = {}  # Seuils individuels par costume
compteur2_active = True
last_game_number_received = 0  # Dernier numéro reçu du canal source
processed_game_numbers: Set[int] = set()  # Anti-doublon : jeux déjà traités

# Debounce : attend que le message soit stable avant de traiter
debounce_tasks: Dict[int, 'asyncio.Task'] = {}   # game_number → Task en attente
debounce_pending: Dict[int, str] = {}             # game_number → dernière version du texte
DEBOUNCE_DELAY = 5.0                              # secondes d'attente après la dernière édition

# Tracking pour export PDF (du game 1 à 1440)
suits_received: Dict[str, list] = {'♠': [], '♥': [], '♦': [], '♣': []}  # Costumes reçus par numéro
suits_missing: Dict[str, list] = {'♠': [], '♥': [], '♦': [], '♣': []}  # Costumes manquants par numéro
SUITS_DATA_FILE = "suits_data.json"          # Fichier de persistance costumes
PREDICTIONS_DATA_FILE = "predictions_data.json"  # Fichier de persistance prédictions
OUTCOMES_DATA_FILE = "outcomes_data.json"    # Fichier de persistance résultats (PERDU + R3)

# Suivi des résultats PERDU et ✅3️⃣ GAGNÉ pour le 3e PDF
predictions_lost: List[Dict] = []   # {'game': N, 'suit': '♦'}
predictions_r3: List[Dict] = []     # {'game': N, 'suit': '♦'}

# NOUVEAU: Compteur1 - Gestion des costumes présents consécutifs
compteur1_trackers: Dict[str, 'Compteur1Tracker'] = {}
compteur1_history: List[Dict] = []  # Historique des séries ≥3
MIN_CONSECUTIVE_FOR_STATS = 3  # Minimum pour apparaître dans /stats

# Gestion des écarts entre prédictions
MIN_GAP_BETWEEN_PREDICTIONS = 3  # Écart minimum entre 2 prédictions
last_prediction_number_sent = 0  # Dernier numéro de prédiction envoyé

# Historiques pour la commande /history
finalized_messages_history: List[Dict] = []
MAX_HISTORY_SIZE = 50
prediction_history: List[Dict] = []

# File d'attente de prédictions (plusieurs prédictions possibles)
prediction_queue: List[Dict] = []  # File ordonnée des prédictions en attente
PREDICTION_SEND_AHEAD = 2  # Envoyer la prédiction quand canal source est à N-2

# Canal secondaire pour redirection Compteur2
COMPTEUR2_CHANNEL_ID = None     # Canal spécifique pour Compteur2

# Réactions dynamiques sur messages finalisés (win/loss)
reaction_msgs: Dict[int, dict] = {}

WIN_REACTION_EMOJIS  = ['🔥', '❤️', '👍🏻', '🎉', '💪', '🏆', '⭐', '✨', '💯', '🚀', '💎', '👑', '🌟']
LOSS_REACTION_EMOJIS = ['💪', '🙏', '😔', '💭', '🤝', '⚡', '🎯']

# ============================================================================
# SYSTÈME DE PAUSE PAR CYCLE (CORRIGÉ)
# ============================================================================

# État de la pause
pause_active = False
pause_counter = 0  # Compteur de prédictions (1-4)
pause_cycle_index = 0  # Index dans le cycle (0, 1, 2...)
pause_message_id = None  # ID du message de pause à éditer
pause_end_time = None  # Heure de fin de pause
pause_task = None  # Tâche de mise à jour du message

# Configuration pause
PAUSE_CYCLE = [3, 5, 4]  # Durées en minutes par défaut
PREDICTIONS_BEFORE_PAUSE = 4  # Nombre de prédictions avant pause

# Expressions de reprise (20 expressions par défaut)
RESUME_EXPRESSIONS = [
    "🎉 Bingo ! Les prédictions reprennent ! Bot créé par Sossou Kouamé",
    "🚀 C'est reparti mon kiki ! Sossou Kouamé vous présente la suite",
    "🎰 La pause est finie, le jeu continue ! By Sossou Kouamé",
    "🔥 De retour en action ! Bot by Sossou Kouamé",
    "⚡ Énergie rechargée à 100% ! Sossou Kouamé au rapport",
    "🎯 Viser juste, viser fort ! Les prédictions reprennent - Sossou Kouamé",
    "🌟 Le spectacle continue ! Bot Telegram de Sossou Kouamé",
    "💫 Et c'est reparti pour un tour ! Sossou Kouamé vous souhaite bonne chance",
    "🎊 Fin de la sieste, début des gains ! By Sossou Kouamé",
    "⏰ L'heure de prédire a sonné ! Sossou Kouamé est de retour",
    "🍀 La chance sourit aux audacieux ! Reprise par Sossou Kouamé",
    "🎵 Tadam ! Les prédictions sont de retour - Sossou Kouamé",
    "🌈 Arc-en-ciel de victoires en vue ! Bot by Sossou Kouamé",
    "🎖️ Médaille de la patience décernée ! Reprise Sossou Kouamé",
    "🚀 Décollage immédiat ! Sossou Kouamé aux commandes",
    "🎩 Abracadabra ! Les prédictions réapparaissent - By Sossou Kouamé",
    "🔮 La boule de cristal est de nouveau claire ! Sossou Kouamé",
    "⚔️ À l'attaque ! Le bot de Sossou Kouamé reprend du service",
    "🎰 Jackpot en approche ! Sossou Kouamé vous y mène",
    "🌟 Étoile filante de prédictions ! Sossou Kouamé fait le show"
]

# ============================================================================
# FONCTION UTILITAIRE - Conversion ID Canal
# ============================================================================

def normalize_channel_id(channel_id) -> int:
    if not channel_id:
        return None
    
    channel_str = str(channel_id)
    
    if channel_str.startswith('-100'):
        return int(channel_str)
    
    if channel_str.startswith('-'):
        return int(channel_str)
    
    return int(f"-100{channel_str}")

async def resolve_channel(entity_id):
    try:
        if not entity_id:
            return None
        
        normalized_id = normalize_channel_id(entity_id)
        entity = await client.get_entity(normalized_id)
        
        if hasattr(entity, 'broadcast') and entity.broadcast:
            logger.info(f"✅ Canal résolu: {entity.title} (ID: {normalized_id})")
            return entity
        
        if hasattr(entity, 'megagroup') and entity.megagroup:
            logger.info(f"✅ Groupe résolu: {entity.title} (ID: {normalized_id})")
            return entity
            
        return entity
        
    except Exception as e:
        logger.error(f"❌ Impossible de résoudre le canal {entity_id}: {e}")
        return None

# ============================================================================
# CLASSES TRACKERS
# ============================================================================

@dataclass
class Compteur2Tracker:
    """Tracker pour le compteur2 (costumes manquants dans 1er groupe)."""
    def __init__(self, suit: str):
        self.suit = suit
        self.counter = 0
        self.last_increment_game = 0
    
    def get_display_name(self) -> str:
        names = {
            '♠': '♠️ Pique',
            '♥': '❤️ Cœur',
            '♦': '♦️ Carreau',
            '♣': '♣️ Trèfle'
        }
        return names.get(self.suit, self.suit)
    
    def increment(self, game_number: int):
        self.counter += 1
        self.last_increment_game = game_number
        logger.info(f"📊 Compteur2 {self.suit}: {self.counter} (incrémenté au jeu #{game_number})")
    
    def reset(self, game_number: int, reason: str = "trouvé"):
        if self.counter > 0:
            logger.info(f"🔄 Compteur2 {self.suit}: reset de {self.counter} à 0 ({reason} au jeu #{game_number})")
        self.counter = 0
        self.last_increment_game = 0
    
    def check_threshold(self, seuil_B: int) -> bool:
        return self.counter >= seuil_B

# NOUVEAU: Compteur1 Tracker (costumes présents consécutifs)
@dataclass
class Compteur1Tracker:
    """Tracker pour le compteur1 (costumes présents consécutivement)."""
    suit: str
    counter: int = 0
    start_game: int = 0  # Jeu où la série a commencé
    last_game: int = 0   # Dernier jeu où vu
    
    def get_display_name(self) -> str:
        names = {
            '♠': '♠️ Pique',
            '♥': '❤️ Cœur',
            '♦': '♦️ Carreau',
            '♣': '♣️ Trèfle'
        }
        return names.get(self.suit, self.suit)
    
    def increment(self, game_number: int):
        if self.counter == 0:
            self.start_game = game_number
        self.counter += 1
        self.last_game = game_number
        logger.info(f"🎯 Compteur1 {self.suit}: {self.counter} consécutifs (jeu #{game_number})")
    
    def reset(self, game_number: int):
        # Sauvegarder dans l'historique si ≥ 3 avant reset
        if self.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(self.suit, self.counter, self.start_game, self.last_game)
        
        if self.counter > 0:
            logger.info(f"🔄 Compteur1 {self.suit}: reset de {self.counter} à 0 (manqué au jeu #{game_number})")
        self.counter = 0
        self.start_game = 0
        self.last_game = 0
    
    def get_status(self) -> str:
        if self.counter == 0:
            return "0"
        return f"{self.counter} (depuis #{self.start_game})"

# ============================================================================
# FONCTIONS COMPTeur1 (NOUVEAU)
# ============================================================================

def save_compteur1_series(suit: str, count: int, start_game: int, end_game: int):
    """Sauvegarde une série de Compteur1 dans l'historique."""
    global compteur1_history
    
    entry = {
        'suit': suit,
        'count': count,
        'start_game': start_game,
        'end_game': end_game,
        'timestamp': datetime.now()
    }
    
    compteur1_history.insert(0, entry)
    
    # Garder seulement les 100 dernières entrées
    if len(compteur1_history) > 100:
        compteur1_history = compteur1_history[:100]
    
    logger.info(f"💾 Série Compteur1 sauvegardée: {suit} {count} fois (jeux #{start_game}-#{end_game})")

def get_compteur1_stats() -> Dict[str, List[Dict]]:
    """Organise l'historique par costume."""
    stats = {'♥': [], '♠': [], '♦': [], '♣': []}
    
    for entry in compteur1_history:
        suit = entry['suit']
        if suit in stats:
            stats[suit].append(entry)
    
    return stats

def get_compteur1_record(suit: str) -> int:
    """Retourne le record (max consécutifs) pour un costume."""
    max_count = 0
    for entry in compteur1_history:
        if entry['suit'] == suit and entry['count'] > max_count:
            max_count = entry['count']
    return max_count

def update_compteur1(game_number: int, first_group: str):
    """Met à jour le Compteur1 basé sur les costumes présents."""
    global compteur1_trackers
    
    suits_in_first = set(get_suits_in_group(first_group))
    
    for suit in ALL_SUITS:
        tracker = compteur1_trackers[suit]
        
        if suit in suits_in_first:
            # Costume présent → incrémenter
            tracker.increment(game_number)
        else:
            # Costume manquant → reset (et sauvegarder si nécessaire)
            tracker.reset(game_number)

# ============================================================================
# FONCTIONS D'HISTORIQUE
# ============================================================================

def add_to_history(game_number: int, message_text: str, first_group: str, suits_found: List[str]):
    global finalized_messages_history
    
    entry = {
        'timestamp': datetime.now(),
        'game_number': game_number,
        'message_text': message_text[:200],
        'first_group': first_group,
        'suits_found': suits_found,
        'predictions_verified': []
    }
    
    finalized_messages_history.insert(0, entry)
    
    if len(finalized_messages_history) > MAX_HISTORY_SIZE:
        finalized_messages_history = finalized_messages_history[:MAX_HISTORY_SIZE]

def add_prediction_to_history(game_number: int, suit: str, verification_games: List[int], prediction_type: str = 'standard'):
    global prediction_history
    
    prediction_history.insert(0, {
        'predicted_game': game_number,
        'suit': suit,
        'predicted_at': datetime.now(),
        'verification_games': verification_games,
        'status': 'en_cours',
        'verified_at': None,
        'verified_by_game': None,
        'rattrapage_level': 0,
        'verified_by': [],
        'type': prediction_type
    })
    
    if len(prediction_history) > MAX_HISTORY_SIZE:
        prediction_history = prediction_history[:MAX_HISTORY_SIZE]

def update_prediction_in_history(game_number: int, suit: str, verified_by_game: int, 
                                verified_by_group: str, rattrapage_level: int, final_status: str):
    global finalized_messages_history, prediction_history
    
    for pred in prediction_history:
        if pred['predicted_game'] == game_number and pred['suit'] == suit:
            pred['verified_by'].append({
                'game_number': verified_by_game,
                'first_group': verified_by_group,
                'rattrapage_level': rattrapage_level
            })
            pred['status'] = final_status
            pred['verified_at'] = datetime.now()
            pred['verified_by_game'] = verified_by_game
            pred['rattrapage_level'] = rattrapage_level
            break
    
    for msg in finalized_messages_history:
        if msg['game_number'] == verified_by_game:
            msg['predictions_verified'].append({
                'predicted_game': game_number,
                'suit': suit,
                'rattrapage_level': rattrapage_level
            })
            break

# ============================================================================
# INITIALISATION
# ============================================================================

def save_suits_data():
    """Sauvegarde suits_received et suits_missing dans un fichier JSON."""
    import json, os
    try:
        data = {
            "suits_received": {k: v for k, v in suits_received.items()},
            "suits_missing":  {k: v for k, v in suits_missing.items()},
        }
        with open(SUITS_DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        logger.error(f"❌ Erreur sauvegarde suits_data: {e}")


def load_suits_data():
    """Charge suits_received et suits_missing depuis le fichier JSON (si présent)."""
    import json, os
    global suits_received, suits_missing
    if not os.path.exists(SUITS_DATA_FILE):
        return
    try:
        with open(SUITS_DATA_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        for suit in ALL_SUITS:
            suits_received[suit] = data.get("suits_received", {}).get(suit, [])
            suits_missing[suit]  = data.get("suits_missing",  {}).get(suit, [])
        total = sum(len(v) for v in suits_received.values())
        logger.info(f"📂 suits_data chargé — {total} entrées reçues restaurées")
    except Exception as e:
        logger.error(f"❌ Erreur chargement suits_data: {e}")


def clear_suits_data():
    """Supprime le fichier de persistance (appelé lors d'un reset complet)."""
    import os
    try:
        if os.path.exists(SUITS_DATA_FILE):
            os.remove(SUITS_DATA_FILE)
            logger.info("🗑️ suits_data.json supprimé (reset)")
    except Exception as e:
        logger.error(f"❌ Erreur suppression suits_data: {e}")


def _dt_to_str(dt) -> str:
    """Convertit un datetime en string ISO, ou None."""
    if dt is None:
        return None
    if isinstance(dt, datetime):
        return dt.isoformat()
    return str(dt)

def _str_to_dt(s) -> Optional[datetime]:
    """Convertit un string ISO en datetime, ou None."""
    if not s:
        return None
    try:
        return datetime.fromisoformat(s)
    except Exception:
        return None


def save_predictions_data():
    """Sauvegarde pending_predictions, prediction_queue et last_prediction_number_sent."""
    import json
    try:
        # Sérialisation des pending_predictions (les datetime → str)
        preds_serial = {}
        for k, v in pending_predictions.items():
            entry = dict(v)
            entry['sent_time'] = _dt_to_str(entry.get('sent_time'))
            preds_serial[str(k)] = entry

        # Sérialisation de prediction_queue
        queue_serial = []
        for item in prediction_queue:
            e = dict(item)
            e['added_at'] = _dt_to_str(e.get('added_at'))
            queue_serial.append(e)

        data = {
            "pending_predictions": preds_serial,
            "prediction_queue": queue_serial,
            "last_prediction_number_sent": last_prediction_number_sent,
        }
        with open(PREDICTIONS_DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        logger.error(f"❌ Erreur sauvegarde predictions_data: {e}")


def load_predictions_data():
    """Charge pending_predictions, prediction_queue et last_prediction_number_sent."""
    import json, os
    global pending_predictions, prediction_queue, last_prediction_number_sent
    if not os.path.exists(PREDICTIONS_DATA_FILE):
        return
    try:
        with open(PREDICTIONS_DATA_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)

        # Restaurer pending_predictions
        loaded_preds = {}
        for k, v in data.get("pending_predictions", {}).items():
            entry = dict(v)
            entry['sent_time'] = _str_to_dt(entry.get('sent_time'))
            loaded_preds[int(k)] = entry
        pending_predictions = loaded_preds

        # Restaurer prediction_queue
        loaded_queue = []
        for item in data.get("prediction_queue", []):
            e = dict(item)
            e['added_at'] = _str_to_dt(e.get('added_at'))
            loaded_queue.append(e)
        prediction_queue = loaded_queue

        # Restaurer last_prediction_number_sent
        last_prediction_number_sent = int(data.get("last_prediction_number_sent", 0))

        logger.info(
            f"📂 predictions_data chargé — "
            f"{len(pending_predictions)} en cours, "
            f"{len(prediction_queue)} en file, "
            f"dernier envoyé: #{last_prediction_number_sent}"
        )
    except Exception as e:
        logger.error(f"❌ Erreur chargement predictions_data: {e}")


def clear_predictions_data():
    """Supprime le fichier de persistance prédictions (appelé lors d'un reset complet)."""
    import os
    try:
        if os.path.exists(PREDICTIONS_DATA_FILE):
            os.remove(PREDICTIONS_DATA_FILE)
            logger.info("🗑️ predictions_data.json supprimé (reset)")
    except Exception as e:
        logger.error(f"❌ Erreur suppression predictions_data: {e}")


def save_outcomes_data():
    """Sauvegarde predictions_lost et predictions_r3 dans un fichier JSON."""
    import json
    try:
        data = {"predictions_lost": predictions_lost, "predictions_r3": predictions_r3}
        with open(OUTCOMES_DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception as e:
        logger.error(f"❌ Erreur sauvegarde outcomes_data: {e}")


def load_outcomes_data():
    """Charge predictions_lost et predictions_r3 depuis le fichier JSON."""
    import json, os
    global predictions_lost, predictions_r3
    if not os.path.exists(OUTCOMES_DATA_FILE):
        return
    try:
        with open(OUTCOMES_DATA_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        predictions_lost = data.get("predictions_lost", [])
        predictions_r3   = data.get("predictions_r3", [])
        logger.info(f"📂 outcomes_data chargé — {len(predictions_lost)} perdus, {len(predictions_r3)} R3")
    except Exception as e:
        logger.error(f"❌ Erreur chargement outcomes_data: {e}")


def clear_outcomes_data():
    """Supprime le fichier de persistance outcomes (appelé lors d'un reset complet)."""
    import os
    try:
        if os.path.exists(OUTCOMES_DATA_FILE):
            os.remove(OUTCOMES_DATA_FILE)
            logger.info("🗑️ outcomes_data.json supprimé (reset)")
    except Exception as e:
        logger.error(f"❌ Erreur suppression outcomes_data: {e}")


def initialize_trackers():
    """Initialise les trackers Compteur1 et Compteur2, et restaure les données PDF."""
    global compteur2_trackers, compteur1_trackers
    
    for suit in ALL_SUITS:
        compteur2_trackers[suit] = Compteur2Tracker(suit=suit)
        compteur1_trackers[suit] = Compteur1Tracker(suit=suit)
        logger.info(f"📊 Trackers {suit}: Compteur1 & Compteur2 initialisés")
    
    load_suits_data()
    load_predictions_data()
    load_outcomes_data()

def is_message_finalized(message: str) -> bool:
    if '⏰' in message:
        return False
    return '✅' in message or '🔰' in message

def is_message_being_edited(message: str) -> bool:
    return '⏰' in message

def extract_parentheses_groups(message: str) -> List[str]:
    scored_groups = re.findall(r"(\d+)?\(([^)]*)\)", message)
    if scored_groups:
        return [f"{score}:{content}" if score else content for score, content in scored_groups]
    return re.findall(r"\(([^)]*)\)", message)

def extract_first_group_only(message: str) -> str:
    """Extrait UNIQUEMENT le premier groupe de parenthèses."""
    start = message.find('(')
    if start == -1:
        return ""
    end = message.find(')', start)
    if end == -1:
        return ""
    return message[start:end+1]

def normalize_suits(text: str) -> str:
    """Normalise les variantes d'emoji de costumes en symboles standard."""
    for old, new in [('❤️', '♥'), ('❤', '♥'), ('♥️', '♥'),
                     ('♠️', '♠'), ('♦️', '♦'), ('♣️', '♣')]:
        text = text.replace(old, new)
    return text

def get_suits_in_group(group_str: str) -> List[str]:
    if ':' in group_str:
        group_str = group_str.split(':', 1)[1]
    normalized = normalize_suits(group_str)
    return [suit for suit in ALL_SUITS if suit in normalized]

def get_first_suit_group(message: str) -> str:
    """Retourne le contenu du PREMIER groupe de parenthèses contenant au moins un costume.
    Si aucun groupe ne contient de costume, retourne le premier groupe trouvé."""
    groups = extract_parentheses_groups(message)
    if not groups:
        return ""
    # Cherche le premier groupe qui contient au moins un costume
    for grp in groups:
        content = grp.split(':', 1)[1] if ':' in grp else grp
        normalized = normalize_suits(content)
        if any(suit in normalized for suit in ALL_SUITS):
            logger.debug(f"🎯 Premier groupe avec costumes: '{content[:40]}'")
            return grp
    # Aucun groupe avec costume : retourne quand même le premier
    logger.warning(f"⚠️ Aucun groupe avec costume trouvé dans le message")
    return groups[0]

def block_suit(suit: str, minutes: int = 5):
    suit_block_until[suit] = datetime.now() + timedelta(minutes=minutes)
    logger.info(f"🔒 {suit} bloqué {minutes}min")

# ============================================================================
# SYSTÈME DE PAUSE - GESTION (CORRIGÉ)
# ============================================================================

def format_pause_message(duration_min: int, remaining_seconds: int) -> str:
    """Formate le message de pause avec temps dynamique."""
    if remaining_seconds <= 0:
        return f"""⏸️ PAUSE TERMINÉE

✅ Fin de la pause
🔄 Préparation de la reprise...

🤖 Baccarat AI"""
    
    minutes = remaining_seconds // 60
    seconds = remaining_seconds % 60
    
    return f"""⏸️ PAUSE ACTIVE

🕐 Durée: {duration_min} minutes
⏳ Temps restant: {minutes}:{seconds:02d}

🤖 Baccarat AI"""

def format_resume_message() -> str:
    """Choisit une expression aléatoire de reprise."""
    return random.choice(RESUME_EXPRESSIONS)

async def update_pause_message(duration_min: int, remaining_seconds: int):
    """Met à jour le message de pause en temps réel."""
    global pause_message_id, pause_active, pause_end_time
    
    if not pause_active or not pause_message_id:
        return
    
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if not prediction_entity:
            return
        
        display_seconds = max(0, remaining_seconds)
        msg = format_pause_message(duration_min, display_seconds)
        
        await client.edit_message(prediction_entity, pause_message_id, msg, parse_mode='markdown')
        
    except Exception as e:
        logger.error(f"❌ Erreur mise à jour pause: {e}")

async def pause_countdown_task(duration_min: int):
    """Tâche qui met à jour le message de pause chaque seconde."""
    global pause_active, pause_message_id, pause_end_time
    
    total_seconds = duration_min * 60
    
    for i in range(total_seconds, 0, -1):
        if not pause_active:
            logger.info("⏸️ Pause annulée manuellement")
            return
        
        await update_pause_message(duration_min, i)
        await asyncio.sleep(1)
    
    if pause_active:
        logger.info("⏸️ Temps écoulé, fin de pause automatique")
        await end_pause()

async def start_pause():
    """Démarre une pause (appelé manuellement via /pause on ou par fin de cycle)."""
    global pause_active, pause_counter, pause_cycle_index, pause_message_id, pause_end_time, pause_task
    
    if pause_active:
        logger.warning("⏸️ Pause déjà active")
        return
    
    if pending_predictions:
        logger.warning(f"⏸️ start_pause: {len(pending_predictions)} prédiction(s) encore active(s), pause reportée")
        return
    
    duration = PAUSE_CYCLE[pause_cycle_index % len(PAUSE_CYCLE)]
    
    pause_active = True
    pause_end_time = datetime.now() + timedelta(minutes=duration)
    
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity:
            msg = format_pause_message(duration, duration * 60)
            sent = await client.send_message(prediction_entity, msg, parse_mode='markdown')
            pause_message_id = sent.id
            
            pause_task = asyncio.create_task(pause_countdown_task(duration))
            
            logger.info(f"⏸️ PAUSE DÉMARRÉE: {duration} min (cycle index: {pause_cycle_index})")
    except Exception as e:
        logger.error(f"❌ Erreur démarrage pause: {e}")
        pause_active = False

async def end_pause():
    """Termine la pause et envoie message de reprise."""
    global pause_active, pause_counter, pause_cycle_index, pause_message_id, pause_end_time, pause_task
    
    if not pause_active:
        return
    
    pause_active = False
    pause_counter = 0
    pause_cycle_index += 1
    pause_end_time = None
    
    if pause_task and not pause_task.done():
        pause_task.cancel()
        try:
            await pause_task
        except asyncio.CancelledError:
            pass
    
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity and pause_message_id:
            resume_msg = format_resume_message()
            
            await client.edit_message(
                prediction_entity, 
                pause_message_id, 
                f"✅ **PAUSE TERMINÉE**\n\n{resume_msg}", 
                parse_mode='markdown'
            )
            
            logger.info(f"▶️ PAUSE TERMINÉE - Reprise avec: {resume_msg[:50]}...")
            
            pause_message_id = None
            
            if prediction_queue:
                logger.info(f"📤 {len(prediction_queue)} prédictions en attente, traitement...")
                await process_prediction_queue(current_game_number)
                
    except Exception as e:
        logger.error(f"❌ Erreur fin pause: {e}")

def increment_pause_counter():
    """Incrémente le compteur de pause et vérifie si pause nécessaire."""
    global pause_counter, pause_active
    
    if pause_active:
        return False
    
    pause_counter += 1
    logger.info(f"⏸️ Compteur pause: {pause_counter}/{PREDICTIONS_BEFORE_PAUSE}")
    
    if pause_counter >= PREDICTIONS_BEFORE_PAUSE:
        logger.info("⏸️ Seuil atteint, pause programmée après vérification")
        return True
    
    return False

async def check_and_trigger_pause(game_number: int):
    """Vérifie si une prédiction terminée doit déclencher la pause.
    La pause ne démarre que lorsque toutes les prédictions en cours sont vérifiées."""
    global pause_counter, pause_active
    
    if pause_active:
        return
    
    if pause_counter >= PREDICTIONS_BEFORE_PAUSE:
        # Attendre que TOUTES les prédictions en cours soient terminées
        if pending_predictions:
            remaining = list(pending_predictions.keys())
            logger.info(f"⏸️ Pause en attente — prédictions encore actives: {remaining}")
            return
        
        await start_pause()

# ============================================================================
# GESTION DES PRÉDICTIONS - MESSAGES SIMPLIFIÉS
# ============================================================================

def format_prediction_message(game_number: int, suit: str, status: str = 'en_cours', 
                             current_check: int = None, verified_games: List[int] = None,
                             rattrapage: int = 0) -> str:
    suit_display = SUIT_DISPLAY.get(suit, suit)
    
    if status == 'en_cours':
        # Carrés de vérification : on n'affiche que les jeux >= current_check
        # Si current_check is None → état initial, on affiche les 4 avec 🔵 sur game_number
        verif_parts = []
        effective = current_check if current_check is not None else game_number
        for i in range(4):
            check_num = game_number + i
            if check_num < effective:
                continue  # jeu déjà vérifié (et raté) → retiré
            elif check_num == effective:
                verif_parts.append(f"🔵{check_num}")
            else:
                verif_parts.append(f"⬜{check_num}")
        
        verif_line = " | ".join(verif_parts)
        
        if current_check is None:
            statut_line = "⏳ En cours:⌛"
        else:
            statut_line = f"⏳ En cours:🔎{current_check}⌛"
        
        return (
            f"🎯 Prédiction #{game_number}\n"
            f"🃏 Couleur : {suit_display}\n"
            f"{statut_line} \n"
            f" {verif_line}"
        )
    
    elif status == 'gagne':
        num_emoji = {0: '0️⃣', 1: '1️⃣', 2: '2️⃣', 3: '3️⃣'}.get(rattrapage, f'{rattrapage}')
        return (
            f"🏆 PRÉDICTION #{game_number}\n\n"
            f"🎯 Couleur: {suit_display}\n"
            f"✅ Statut: ✅{num_emoji} GAGNÉ"
        )
    
    elif status == 'perdu':
        return (
            f"🏆 PRÉDICTION #{game_number}\n\n"
            f"🎯 Couleur: {suit_display}\n"
            f"✅ Statut: ❌ PERDU"
        )
    
    return ""

def get_initial_counts(is_win: bool) -> dict:
    """Génère les compteurs de réactions initiaux avec sélection aléatoire d'emojis."""
    emoji_pool = WIN_REACTION_EMOJIS if is_win else LOSS_REACTION_EMOJIS
    # Sélectionne 2-3 emojis aléatoires (différents à chaque fois)
    num_emojis = random.randint(2, min(3, len(emoji_pool)))
    selected_emojis = random.sample(emoji_pool, num_emojis)
    # Génère des compteurs variés initiaux
    return {e: random.randint(5, 50) for e in selected_emojis}

def build_reaction_line(counts: dict) -> str:
    """Construit la ligne de réactions emoji."""
    return '   '.join(f"{e} {c}" for e, c in counts.items())

def format_final_message(game_number: int, suit: str, rattrapage: int, is_win: bool) -> str:
    """Formate le message final (win/loss) — réactions natives Telegram."""
    suit_display = SUIT_DISPLAY.get(suit, suit)
    if is_win:
        num_emoji = {0: '0️⃣', 1: '1️⃣', 2: '2️⃣', 3: '3️⃣'}.get(rattrapage, str(rattrapage))
        return (
            f"🏆 PRÉDICTION #{game_number}\n\n"
            f"🎯 Couleur: {suit_display}\n"
            f"✅ Statut: ✅{num_emoji} GAGNÉ"
        )
    else:
        return (
            f"🏆 PRÉDICTION #{game_number}\n\n"
            f"🎯 Couleur: {suit_display}\n"
            f"✅ Statut: ❌ PERDU"
        )

async def add_native_reactions(channel_id: int, msg_id: int, emojis: list):
    """Ajoute les réactions natives Telegram au message."""
    if not emojis or not msg_id:
        logger.warning(f"⚠️ Réactions non ajoutées (msg_id={msg_id}, emojis={emojis})")
        return
    try:
        entity = await resolve_channel(channel_id)
        if not entity:
            logger.error(f"❌ Canal non résolu: {channel_id}")
            return
        logger.info(f"🔄 Ajout réactions natives #{msg_id}: {emojis}")
        for emoji in emojis:
            try:
                # Telethon API pour réactions natives
                await client.send_reaction(entity, msg_id, emoji, big=True)
                logger.info(f"✅ Réaction ajoutée: {emoji} #{msg_id}")
                await asyncio.sleep(0.2)  # Évite le flood
            except Exception as e:
                logger.warning(f"⚠️ Réaction {emoji} #{msg_id}: {e}")
    except Exception as e:
        logger.error(f"❌ Erreur ajout réactions natives: {e}")

async def reaction_update_task():
    """Met à jour les réactions dynamiquement sur les messages finalisés jusqu'à 1440 min."""
    while True:
        try:
            await asyncio.sleep(60)
            for game_num in list(reaction_msgs.keys()):
                info = reaction_msgs.get(game_num)
                if not info:
                    continue
                # Arrête après 1440 minutes (10h)
                if info['update_count'] >= 1440:
                    logger.info(f"⏹️ Réactions finalisées #{game_num} (1440 min atteint)")
                    del reaction_msgs[game_num]
                    continue
                
                # Ajoute occasionnellement un nouvel emoji (effet animation toutes les 5 min)
                if info['update_count'] % 5 == 0 and random.random() < 0.4:
                    emoji_pool = WIN_REACTION_EMOJIS if info['is_win'] else LOSS_REACTION_EMOJIS
                    available = [e for e in emoji_pool if e not in info['emojis']]
                    if available:
                        new_emoji = random.choice(available)
                        info['emojis'].append(new_emoji)
                        # Ajoute la réaction native au message
                        try:
                            pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                            if pred_entity and info.get('msg_id'):
                                await client.send_reaction(pred_entity, info['msg_id'], new_emoji, big=True)
                        except Exception as e:
                            logger.warning(f"⚠️ Réaction native {new_emoji}: {e}")
                        if info.get('secondary_msg_id') and info.get('secondary_channel_id'):
                            try:
                                sec_entity = await resolve_channel(info['secondary_channel_id'])
                                if sec_entity:
                                    await client.send_reaction(sec_entity, info['secondary_msg_id'], new_emoji, big=True)
                            except Exception as e:
                                logger.warning(f"⚠️ Réaction native sec {new_emoji}: {e}")
                
                info['update_count'] += 1
        except Exception as e:
            logger.error(f"❌ Erreur reaction_update_task: {e}")

# ============================================================================
# ENVOI MULTI-CANAUX
# ============================================================================

async def send_prediction_to_channel(channel_id: int, game_number: int, suit: str, 
                                    prediction_type: str, is_secondary: bool = False) -> Optional[int]:
    try:
        if not is_secondary and suit in suit_block_until and datetime.now() < suit_block_until[suit]:
            logger.info(f"🔒 {suit} bloqué, prédiction annulée")
            return None
        
        if not channel_id:
            return None
        
        channel_entity = await resolve_channel(channel_id)
        if not channel_entity:
            logger.error(f"❌ Canal {channel_id} inaccessible")
            return None
        
        msg = format_prediction_message(game_number, suit, 'en_cours', None, [])
        
        sent = await client.send_message(channel_entity, msg, parse_mode='markdown')
        logger.info(f"✅ Envoyé à {'canal secondaire' if is_secondary else 'canal principal'} {channel_id}: #{game_number} {suit}")
        return sent.id
        
    except ChatWriteForbiddenError:
        logger.error(f"❌ Pas de permission dans {channel_id}")
        return None
    except UserBannedInChannelError:
        logger.error(f"❌ Bot banni de {channel_id}")
        return None
    except Exception as e:
        logger.error(f"❌ Erreur envoi à {channel_id}: {e}")
        return None

async def send_prediction_multi_channel(game_number: int, suit: str, prediction_type: str = 'standard') -> bool:
    """Envoie la prédiction au canal principal ET au canal secondaire Compteur2."""
    global last_prediction_time, last_prediction_number_sent, COMPTEUR2_CHANNEL_ID
    
    success = False
    
    if PREDICTION_CHANNEL_ID:
        # ── VERROU SYNCHRONE ─────────────────────────────────────────────────
        # Réserver la place dans pending_predictions AVANT tout await.
        # Si une autre tâche asyncio tourne pendant les awaits ci-dessous,
        # elle verra pending_predictions non vide et ne lancera pas de 2e prédiction.
        if game_number in pending_predictions:
            logger.warning(f"⚠️ #{game_number} déjà réservé dans pending, envoi annulé")
            return False
        
        old_last = last_prediction_number_sent
        last_prediction_number_sent = game_number  # gap check immédiatement effectif
        
        pending_predictions[game_number] = {
            'suit': suit,
            'message_id': None,        # sera mis à jour après l'envoi Telegram
            'status': 'sending',       # placeholder — bloque les vérifications concurrentes
            'type': prediction_type,
            'sent_time': datetime.now(),
            'verification_games': [game_number, game_number + 1, game_number + 2, game_number + 3],
            'verified_games': [],
            'found_at': None,
            'rattrapage': 0,
            'current_check': game_number
        }
        # ── FIN VERROU SYNCHRONE ─────────────────────────────────────────────
        
        msg_id = await send_prediction_to_channel(
            PREDICTION_CHANNEL_ID, game_number, suit, prediction_type, is_secondary=False
        )
        
        if msg_id:
            last_prediction_time = datetime.now()
            pending_predictions[game_number]['message_id'] = msg_id
            pending_predictions[game_number]['status'] = 'en_cours'
            add_prediction_to_history(game_number, suit, [game_number, game_number + 1, game_number + 2, game_number + 3], prediction_type)
            success = True
            
            # Envoyer au canal secondaire Compteur2 si configuré
            secondary_channel_id = None
            if COMPTEUR2_CHANNEL_ID:
                secondary_channel_id = COMPTEUR2_CHANNEL_ID
            
            if secondary_channel_id:
                sec_msg_id = await send_prediction_to_channel(
                    secondary_channel_id, game_number, suit, prediction_type, is_secondary=True
                )
                if sec_msg_id:
                    pending_predictions[game_number]['secondary_message_id'] = sec_msg_id
                    pending_predictions[game_number]['secondary_channel_id'] = secondary_channel_id
                    logger.info(f"📡 Canal secondaire {secondary_channel_id}: #{game_number} envoyé (msg {sec_msg_id})")
            save_predictions_data()
        else:
            # Envoi échoué — retirer le placeholder pour ne pas bloquer le système
            if game_number in pending_predictions and pending_predictions[game_number]['status'] == 'sending':
                del pending_predictions[game_number]
            last_prediction_number_sent = old_last  # restaurer l'ancien last
            save_predictions_data()
    
    if success and not pause_active:
        need_pause = increment_pause_counter()
        if need_pause:
            logger.info(f"⏸️ La {PREDICTIONS_BEFORE_PAUSE}ème prédiction (#{game_number}) va déclencher la pause après vérification")
    
    return success

async def update_prediction_message(game_number: int, status: str, rattrapage: int = 0):
    """Met à jour le statut d'une prédiction (uniquement canal principal)."""
    global pause_active, pause_counter, pause_cycle_index, pause_message_id, pause_end_time, pause_task
    
    if game_number not in pending_predictions:
        logger.warning(f"⚠️ update_prediction_message: #{game_number} introuvable (déjà traité?)")
        return
    
    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    is_win = 'gagne' in status
    initial_counts = get_initial_counts(is_win)
    initial_emojis = list(initial_counts.keys())
    new_msg = format_final_message(game_number, suit, rattrapage, is_win)
    
    if is_win:
        logger.info(f"✅ Gagné: #{game_number} (R{rattrapage})")
        if rattrapage == 3:
            predictions_r3.append({'game': game_number, 'suit': suit})
            save_outcomes_data()
    else:
        logger.info(f"❌ Perdu: #{game_number}")
        block_suit(suit, 5)
        predictions_lost.append({'game': game_number, 'suit': suit})
        save_outcomes_data()
    
    # ── SECTION SYNCHRONE (aucun await) ─────────────────────────────────────
    # Tout ce qui suit se fait AVANT le premier await.
    # Cela garantit qu'aucune tâche concurrente ne peut s'intercaler.
    
    del pending_predictions[game_number]
    save_predictions_data()
    
    # Si les conditions de pause sont atteintes, verrouiller pause_active = True
    # IMMÉDIATEMENT — avant tout await — pour bloquer les envois concurrents.
    pause_to_start = False
    pause_duration = None
    if not pause_active and pause_counter >= PREDICTIONS_BEFORE_PAUSE and not pending_predictions:
        pause_to_start = True
        pause_duration = PAUSE_CYCLE[pause_cycle_index % len(PAUSE_CYCLE)]
        pause_active = True  # ← VERROU INSTANTANÉ
        pause_end_time = datetime.now() + timedelta(minutes=pause_duration)
        logger.info(f"⏸️ Pause verrouillée ({pause_duration} min) — aucun envoi possible")
    # ── FIN SECTION SYNCHRONE ────────────────────────────────────────────────
    
    # Éditer le message de prédiction — canal principal
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity and msg_id:
            await client.edit_message(prediction_entity, msg_id, new_msg, parse_mode='markdown')
        elif not prediction_entity:
            logger.error("❌ Canal principal inaccessible pour mise à jour")
    except Exception as e:
        logger.error(f"❌ Erreur édition message #{game_number}: {e}")
    
    # Éditer le message de prédiction — canal secondaire (même contenu)
    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        try:
            sec_entity = await resolve_channel(sec_channel_id)
            if sec_entity:
                await client.edit_message(sec_entity, sec_msg_id, new_msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Erreur édition canal secondaire #{game_number}: {e}")
    
    # Réactions natives Telegram - Désactivées (nécessite Telethon 1.36+)
    # await add_native_reactions(PREDICTION_CHANNEL_ID, msg_id, initial_emojis)
    # if sec_msg_id and sec_channel_id:
    #     await add_native_reactions(sec_channel_id, sec_msg_id, initial_emojis)
    
    # Enregistrer pour mises à jour de réactions dynamiques
    reaction_msgs[game_number] = {
        'suit': suit,
        'rattrapage': rattrapage,
        'is_win': is_win,
        'emojis': initial_emojis,
        'msg_id': msg_id,
        'secondary_msg_id': sec_msg_id,
        'secondary_channel_id': sec_channel_id,
        'update_count': 0
    }
    logger.info(f"🔥 Réactions natives ajoutées #{game_number}: {' '.join(initial_emojis)}")

    # Finaliser l'envoi du message de pause si nécessaire
    if pause_to_start:
        try:
            prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
            if prediction_entity:
                pause_msg = format_pause_message(pause_duration, pause_duration * 60)
                sent = await client.send_message(prediction_entity, pause_msg, parse_mode='markdown')
                pause_message_id = sent.id
                pause_task = asyncio.create_task(pause_countdown_task(pause_duration))
                logger.info(f"⏸️ PAUSE DÉMARRÉE: {pause_duration} min (cycle index: {pause_cycle_index})")
        except Exception as e:
            logger.error(f"❌ Erreur envoi message pause: {e}")

async def update_prediction_progress(game_number: int, current_check: int):
    """Met à jour l'affichage de la progression (canal principal uniquement)."""
    if game_number not in pending_predictions:
        return
    
    pred = pending_predictions[game_number]
    suit = pred['suit']
    msg_id = pred['message_id']
    verified_games = pred.get('verified_games', [])
    
    pred['current_check'] = current_check
    rattrapage = pred.get('rattrapage', 0)
    
    msg = format_prediction_message(game_number, suit, 'en_cours', current_check, verified_games, rattrapage)
    
    # Canal principal
    try:
        prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
        if prediction_entity:
            await client.edit_message(prediction_entity, msg_id, msg, parse_mode='markdown')
    except Exception as e:
        logger.error(f"❌ Erreur update progress: {e}")
    
    # Canal secondaire (synchronisation progression)
    sec_msg_id = pred.get('secondary_message_id')
    sec_channel_id = pred.get('secondary_channel_id')
    if sec_msg_id and sec_channel_id:
        try:
            sec_entity = await resolve_channel(sec_channel_id)
            if sec_entity:
                await client.edit_message(sec_entity, sec_msg_id, msg, parse_mode='markdown')
        except Exception as e:
            logger.error(f"❌ Erreur update progress canal secondaire: {e}")

async def check_prediction_result(game_number: int, first_group: str) -> bool:
    suits_in_result = get_suits_in_group(first_group)
    
    if game_number in pending_predictions:
        pred = pending_predictions[game_number]
        if pred['status'] != 'en_cours':
            return False
            
        target_suit = pred['suit']
        
        if game_number in pred['verified_games']:
            return False
        
        # Afficher 🔎game_number dès que la vérification commence
        await update_prediction_progress(game_number, game_number)
        
        pred['verified_games'].append(game_number)
        
        logger.info(f"🔍 Vérification #{game_number}: {target_suit} dans {suits_in_result}?")
        
        if target_suit in suits_in_result:
            await update_prediction_message(game_number, 'gagne', 0)
            update_prediction_in_history(game_number, target_suit, game_number, first_group, 0, 'gagne_r0')
            return True
        else:
            pred['rattrapage'] = 1
            next_check = game_number + 1
            logger.info(f"❌ #{game_number} non trouvé, attente #{next_check}")
            await update_prediction_progress(game_number, next_check)
            return False
    
    for original_game, pred in list(pending_predictions.items()):
        if pred['status'] != 'en_cours':
            continue
            
        target_suit = pred['suit']
        rattrapage = pred.get('rattrapage', 0)
        expected_game = original_game + rattrapage
        
        if game_number == expected_game and rattrapage > 0:
            if game_number in pred['verified_games']:
                return False
            
            pred['verified_games'].append(game_number)
            
            logger.info(f"🔍 Vérification R{rattrapage} #{game_number}: {target_suit} dans {suits_in_result}?")
            
            if target_suit in suits_in_result:
                await update_prediction_message(original_game, 'gagne', rattrapage)
                update_prediction_in_history(original_game, target_suit, game_number, first_group, rattrapage, f'gagne_r{rattrapage}')
                return True
            else:
                if rattrapage < 3:
                    pred['rattrapage'] = rattrapage + 1
                    next_check = original_game + rattrapage + 1
                    logger.info(f"❌ R{rattrapage} échoué, attente #{next_check}")
                    await update_prediction_progress(original_game, next_check)
                    return False
                else:
                    logger.info(f"❌ R3 échoué, prédiction perdue")
                    await update_prediction_message(original_game, 'perdu', 3)
                    update_prediction_in_history(original_game, target_suit, game_number, first_group, 3, 'perdu')
                    return False
    
    return False

# ============================================================================
# GESTION COMPTEUR2
# ============================================================================

def update_compteur2(game_number: int, first_group_content: str):
    """Met à jour Compteur2 (costumes manquants dans le PREMIER groupe UNIQUEMENT)."""
    global compteur2_trackers
    
    # first_group_content est déjà le contenu du premier groupe (ex: "8♣️4♠️Q♦️")
    suits_in_first = set(get_suits_in_group(first_group_content))
    
    # Incrémenter les costumes MANQUANTS du premier groupe, réinitialiser ceux trouvés
    for suit in ALL_SUITS:
        tracker = compteur2_trackers[suit]
        
        if suit in suits_in_first:
            # Costume trouvé dans le 1er groupe : réinitialiser
            tracker.reset(game_number)
        else:
            # Costume manquant du 1er groupe : incrémenter
            tracker.increment(game_number)

def get_compteur2_ready_predictions(current_game: int) -> List[tuple]:
    """Retourne les prédictions prêtes selon Compteur2."""
    global compteur2_trackers, compteur2_seuil_B, compteur2_seuil_by_suit
    
    ready = []
    for suit in ALL_SUITS:
        tracker = compteur2_trackers[suit]
        # Utilise le seuil individuel ou le seuil global par défaut
        seuil = compteur2_seuil_by_suit.get(suit, compteur2_seuil_B)
        
        if tracker.check_threshold(seuil):
            pred_number = current_game + 2
            ready.append((suit, pred_number))
            tracker.reset(current_game, reason=f"seuil B={seuil} atteint → prédiction #{pred_number}")
    
    return ready

# ============================================================================
# GESTION INTELLIGENTE DE LA FILE D'ATTENTE (avec pause)
# ============================================================================

def can_accept_prediction(pred_number: int) -> bool:
    global prediction_queue, pending_predictions, last_prediction_number_sent, MIN_GAP_BETWEEN_PREDICTIONS, pause_active
    
    if pause_active:
        logger.info(f"⛔ En pause, prédiction #{pred_number} rejetée")
        return False
    
    if last_prediction_number_sent > 0:
        gap = pred_number - last_prediction_number_sent
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            logger.info(f"⛔ Écart insuffisant avec dernier envoyé (#{last_prediction_number_sent}): {gap} < {MIN_GAP_BETWEEN_PREDICTIONS}")
            return False
    
    # Vérifier l'écart contre les prédictions actuellement en cours de vérification
    for active_num in pending_predictions:
        gap = abs(pred_number - active_num)
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            logger.info(f"⛔ Écart insuffisant avec prédiction active (#{active_num}): {gap} < {MIN_GAP_BETWEEN_PREDICTIONS}")
            return False
    
    for queued_pred in prediction_queue:
        existing_num = queued_pred['game_number']
        gap = abs(pred_number - existing_num)
        if gap < MIN_GAP_BETWEEN_PREDICTIONS:
            logger.info(f"⛔ Écart insuffisant avec file d'attente (#{existing_num}): {gap} < {MIN_GAP_BETWEEN_PREDICTIONS}")
            return False
    
    return True

def add_to_prediction_queue(game_number: int, suit: str, prediction_type: str) -> bool:
    global prediction_queue, pause_active
    
    if pause_active:
        logger.info(f"⏸️ En pause, #{game_number} non ajouté")
        return False
    
    for pred in prediction_queue:
        if pred['game_number'] == game_number:
            logger.info(f"⚠️ Prédiction #{game_number} déjà dans la file")
            return False
    
    if not can_accept_prediction(game_number):
        logger.info(f"❌ Prédiction #{game_number} rejetée - écart insuffisant")
        return False
    
    new_pred = {
        'game_number': game_number,
        'suit': suit,
        'type': prediction_type,
        'added_at': datetime.now()
    }
    
    prediction_queue.append(new_pred)
    prediction_queue.sort(key=lambda x: x['game_number'])
    save_predictions_data()
    logger.info(f"📥 Prédiction #{game_number} ({suit}) ajoutée à la file. Total: {len(prediction_queue)}")
    return True

async def process_prediction_queue(current_game: int):
    global prediction_queue, pending_predictions, pause_active
    
    if pause_active:
        return
    
    # RÈGLE 1: Jamais de nouvelle prédiction si une est encore en cours de vérification
    if pending_predictions:
        logger.info(f"⏳ {len(pending_predictions)} prédiction(s) en cours, file en attente")
        return
    
    to_remove = []
    to_send = None
    
    for pred in list(prediction_queue):
        pred_number = pred['game_number']
        suit = pred['suit']
        pred_type = pred['type']
        
        # RÈGLE 2: Prédiction expirée — le moment optimal est passé (moins de PREDICTION_SEND_AHEAD jeux restants)
        if current_game > pred_number - PREDICTION_SEND_AHEAD:
            logger.warning(f"⏰ Prédiction #{pred_number} ({suit}) EXPIRÉE — canal à #{current_game}, trop tard")
            to_remove.append(pred)
            continue
        
        # RÈGLE 3: Envoyer uniquement quand on est exactement au bon moment (N-PREDICTION_SEND_AHEAD)
        if current_game == pred_number - PREDICTION_SEND_AHEAD:
            to_send = pred
            break
    
    # Nettoyer les expirées
    for pred in to_remove:
        prediction_queue.remove(pred)
        logger.info(f"🗑️ #{pred['game_number']} retiré (expiré). Restant: {len(prediction_queue)}")
    if to_remove:
        save_predictions_data()
    
    # Envoyer la prédiction retenue
    if to_send:
        pred_number = to_send['game_number']
        suit = to_send['suit']
        pred_type = to_send['type']
        
        # Vérification finale juste avant envoi (protection race condition)
        if pause_active:
            logger.warning(f"⚠️ Pause détectée avant envoi #{pred_number}, annulé")
            return
        if pending_predictions:
            logger.warning(f"⚠️ Prédiction active détectée avant envoi #{pred_number}, annulé")
            return
        
        logger.info(f"📤 Envoi depuis file: #{pred_number} (canal à #{current_game})")
        success = await send_prediction_multi_channel(pred_number, suit, pred_type)
        
        if success:
            prediction_queue.remove(to_send)
            save_predictions_data()
            logger.info(f"✅ #{pred_number} envoyé et retiré de la file. Restant: {len(prediction_queue)}")
        else:
            logger.warning(f"⚠️ Échec envoi #{pred_number}, conservation dans file")

# ============================================================================
# TRAITEMENT DES MESSAGES (CORRIGÉ avec Compteur1)
# ============================================================================

async def process_game_result(game_number: int, message_text: str):
    global current_game_number, last_source_game_number, pause_active, pause_end_time, last_game_number_received
    global suits_received, suits_missing, processed_game_numbers

    # ── Anti-doublon : ignorer un jeu déjà traité (message édité ou dupliqué) ──
    if game_number in processed_game_numbers:
        logger.info(f"⏭️ Jeu #{game_number} déjà traité, ignoré (message édité)")
        return
    processed_game_numbers.add(game_number)
    # Nettoyage pour éviter une croissance infinie (garde les 200 derniers)
    if len(processed_game_numbers) > 200:
        min_game = min(processed_game_numbers)
        processed_game_numbers.discard(min_game)

    current_game_number = game_number
    last_source_game_number = game_number
    last_game_number_received = game_number
    
    # Vérifier si pause expirée
    if pause_active and pause_end_time:
        remaining = (pause_end_time - datetime.now()).total_seconds()
        if remaining <= 0:
            logger.info("⏸️ Pause expirée détectée, reprise automatique")
            await end_pause()
    
    groups = extract_parentheses_groups(message_text)
    if not groups:
        logger.warning(f"⚠️ Pas de groupe trouvé dans #{game_number}")
        return
    
    # Prend le PREMIER groupe contenant des costumes (ignore les parenthèses sans costume)
    first_group = get_first_suit_group(message_text)
    if not first_group:
        logger.warning(f"⚠️ Aucun costume dans les groupes de #{game_number}")
        return
    suits_in_first = get_suits_in_group(first_group)
    logger.info(f"🃏 Jeu #{game_number} premier groupe: '{first_group[:50]}' → costumes: {suits_in_first}")
    
    # Tracker les costumes reçus et manquants (1-1440)
    if 1 <= game_number <= 1440:
        suits_set = set(suits_in_first)
        for suit in ALL_SUITS:
            if suit in suits_set:
                suits_received[suit].append(game_number)
            else:
                suits_missing[suit].append(game_number)
        save_suits_data()
    
    # Reset auto à #1440 - envoyer les PDFs AVANT le reset
    if current_game_number >= 1440:
        logger.warning(f"🚨 #1440 atteint - envoi PDFs automatique")
        await send_pdfs_to_admin()
        await perform_full_reset("🚨 Reset automatique - Numéro #1440 atteint")
        return
    
    logger.info(f"📊 Jeu #{game_number}: {suits_in_first} dans '{first_group[:30]}...'")
    
    add_to_history(game_number, message_text, first_group, suits_in_first)
    
    # NOUVEAU: Mettre à jour Compteur1 (présences consécutives)
    update_compteur1(game_number, first_group)
    
    # Vérification des prédictions existantes
    await check_prediction_result(game_number, first_group)
    
    # Traiter la file d'attente
    await process_prediction_queue(game_number)
    
    if pause_active:
        logger.info(f"⏸️ En pause, pas de nouvelle détection")
        return
    
    # Compteur2
    if compteur2_active:
        update_compteur2(game_number, first_group)
        
        compteur2_preds = get_compteur2_ready_predictions(game_number)
        any_added = False
        for suit, pred_num in compteur2_preds:
            added = add_to_prediction_queue(pred_num, suit, 'compteur2')
            if added:
                logger.info(f"📊 Compteur2: #{pred_num} en file d'attente")
                any_added = True
        
        # Si de nouvelles prédictions ont été ajoutées, traiter la file immédiatement
        # (évite l'expiration au jeu suivant quand le moment d'envoi = jeu courant)
        if any_added and not pause_active:
            await process_prediction_queue(game_number)

async def _debounce_run(game_number: int):
    """Attend DEBOUNCE_DELAY secondes de stabilité puis traite le jeu."""
    global debounce_tasks, debounce_pending
    try:
        await asyncio.sleep(DEBOUNCE_DELAY)
        message_text = debounce_pending.pop(game_number, "")
        debounce_tasks.pop(game_number, None)
        if message_text:
            logger.info(f"⏱️ Débounce OK #{game_number} — traitement de la version finale")
            await process_game_result(game_number, message_text)
    except asyncio.CancelledError:
        pass  # Annulé par une nouvelle édition, normal


async def handle_message(event, is_edit: bool = False):
    global debounce_tasks, debounce_pending
    try:
        chat = await event.get_chat()
        chat_id = chat.id
        
        if hasattr(chat, 'broadcast') and chat.broadcast:
            if not str(chat_id).startswith('-100'):
                chat_id = int(f"-100{abs(chat_id)}")
        
        normalized_source = normalize_channel_id(SOURCE_CHANNEL_ID)
        if chat_id != normalized_source:
            return
        
        message_text = event.message.message
        edit_info = " [EDITÉ]" if is_edit else ""

        # ── Extraire le numéro de jeu dès le début (si présent) ──
        num_match = re.search(r"#N\s*(\d+)", message_text, re.IGNORECASE)
        game_label = f"#N{num_match.group(1)}" if num_match else "?"
        logger.info(f"📨{edit_info} Msg {event.message.id} {game_label}: {message_text[:55]}...")

        # ── Règle unique : le message doit contenir ✅ ou 🔰 pour être traité ──
        if not is_message_finalized(message_text):
            # Pas encore finalisé — on enregistre qu'on attend ce jeu
            if num_match:
                gnum = int(num_match.group(1))
                waiting_finalization[gnum] = {
                    'msg_id': event.message.id,
                    'text': message_text
                }
                status = "⏰ en cours d'édition" if '⏰' in message_text else "pas encore finalisé"
                logger.info(f"⏳ {game_label} {status} — en attente de ✅ ou 🔰")
            return

        # ── Message finalisé (✅ ou 🔰 présent) ──
        if not num_match:
            logger.warning("⚠️ Numéro non trouvé dans message finalisé")
            return

        game_number = int(num_match.group(1))

        # Retirer de la liste d'attente
        waiting_finalization.pop(game_number, None)

        # ── Débounce : annuler le timer précédent et relancer ──
        existing = debounce_tasks.get(game_number)
        if existing and not existing.done():
            existing.cancel()
            logger.info(f"🔄 {game_label} — nouvelle version reçue, débounce remis à zéro")

        # Stocker la version la plus récente et démarrer le timer
        debounce_pending[game_number] = message_text
        debounce_tasks[game_number] = asyncio.create_task(_debounce_run(game_number))
        logger.info(f"⏱️ {game_label} finalisé (✅/🔰) — débounce {DEBOUNCE_DELAY}s avant traitement")
        
    except Exception as e:
        logger.error(f"❌ Erreur handle_message: {e}")
        import traceback
        logger.error(traceback.format_exc())

async def handle_new_message(event):
    await handle_message(event, False)

async def handle_edited_message(event):
    await handle_message(event, True)

# ============================================================================
# RESET ET NOTIFICATIONS (CORRIGÉ)
# ============================================================================

async def notify_admin_reset(reason: str, stats: int, queue_stats: int):
    if not ADMIN_ID or ADMIN_ID == 0:
        logger.warning("⚠️ ADMIN_ID non configuré, impossible de notifier")
        return
    
    try:
        admin_entity = await client.get_entity(ADMIN_ID)
        
        msg = f"""🔄 **RESET SYSTÈME**

{reason}

✅ Compteurs internes remis à zéro
✅ {stats} prédictions actives cleared
✅ {queue_stats} prédictions en file cleared
✅ Nouvelle analyse

🤖 Baccarat AI"""
        
        await client.send_message(admin_entity, msg, parse_mode='markdown')
        logger.info(f"✅ Notification reset envoyée à l'admin {ADMIN_ID}")
        
    except Exception as e:
        logger.error(f"❌ Impossible de notifier l'admin: {e}")

async def cleanup_stale_predictions():
    """Nettoie les prédictions bloquées depuis plus de PREDICTION_TIMEOUT_MINUTES."""
    global pending_predictions
    from config import PREDICTION_TIMEOUT_MINUTES
    
    now = datetime.now()
    stale = []
    
    for game_number, pred in list(pending_predictions.items()):
        sent_time = pred.get('sent_time')
        if sent_time:
            age_minutes = (now - sent_time).total_seconds() / 60
            if age_minutes >= PREDICTION_TIMEOUT_MINUTES:
                stale.append(game_number)
    
    for game_number in stale:
        pred = pending_predictions.get(game_number)
        if pred:
            suit = pred.get('suit', '?')
            age = int((now - pred['sent_time']).total_seconds() / 60)
            logger.warning(f"🧹 Prédiction #{game_number} ({suit}) supprimée — bloquée depuis {age} min (timeout {PREDICTION_TIMEOUT_MINUTES} min)")
            
            # Tenter d'éditer le message pour indiquer l'expiration
            try:
                prediction_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if prediction_entity and pred.get('message_id'):
                    suit_display = SUIT_DISPLAY.get(suit, suit)
                    expired_msg = f"🏆 PRÉDICTION #{game_number}\n\n🎯 Couleur: {suit_display}\n✅ Statut: ⚠️ EXPIRÉE"
                    await client.edit_message(prediction_entity, pred['message_id'], expired_msg, parse_mode='markdown')
            except Exception as e:
                logger.error(f"❌ Impossible d'éditer message expiré #{game_number}: {e}")
            
            del pending_predictions[game_number]
    
    if stale:
        save_predictions_data()
        logger.info(f"🧹 {len(stale)} prédiction(s) expirée(s) nettoyée(s)")


async def auto_reset_system():
    """Mode veille avec vérification de pause bloquée et prédictions expirées."""
    global pause_active, pause_end_time
    
    while True:
        try:
            await asyncio.sleep(60)
            
            # Vérifier pause bloquée
            if pause_active and pause_end_time:
                remaining = (pause_end_time - datetime.now()).total_seconds()
                if remaining <= -30:
                    logger.warning("🚨 Pause bloquée détectée (temps dépassé), auto-correction...")
                    await end_pause()
            
            # Nettoyer les prédictions bloquées (timeout)
            if pending_predictions:
                await cleanup_stale_predictions()
                    
        except Exception as e:
            logger.error(f"❌ Erreur auto_reset: {e}")
            await asyncio.sleep(60)

async def perform_full_reset(reason: str):
    global pending_predictions, last_prediction_time, waiting_finalization
    global last_prediction_number_sent, compteur2_trackers, prediction_queue
    global pause_active, pause_counter, pause_cycle_index, pause_message_id, pause_end_time, pause_task
    global compteur1_trackers, compteur1_history
    global processed_game_numbers, suits_received, suits_missing
    global debounce_tasks, debounce_pending
    global predictions_lost, predictions_r3
    
    stats = len(pending_predictions)
    queue_stats = len(prediction_queue)
    
    # Sauvegarder les séries en cours avant reset
    for tracker in compteur1_trackers.values():
        if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
            save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)
    
    if pause_active:
        pause_active = False
        if pause_task and not pause_task.done():
            pause_task.cancel()
            try:
                await pause_task
            except asyncio.CancelledError:
                pass
        pause_message_id = None
        pause_end_time = None
    
    for tracker in compteur2_trackers.values():
        tracker.counter = 0
        tracker.last_increment_game = 0
    
    for tracker in compteur1_trackers.values():
        tracker.counter = 0
        tracker.start_game = 0
        tracker.last_game = 0
    
    pending_predictions.clear()
    waiting_finalization.clear()
    prediction_queue.clear()
    last_prediction_time = None
    last_prediction_number_sent = 0
    suit_block_until.clear()
    processed_game_numbers.clear()
    suits_received = {'♠': [], '♥': [], '♦': [], '♣': []}
    suits_missing  = {'♠': [], '♥': [], '♦': [], '♣': []}
    predictions_lost.clear()
    predictions_r3.clear()
    clear_suits_data()
    clear_predictions_data()
    clear_outcomes_data()
    # Annuler tous les debounces en cours
    for task in list(debounce_tasks.values()):
        if not task.done():
            task.cancel()
    debounce_tasks.clear()
    debounce_pending.clear()
    
    pause_counter = 0
    pause_cycle_index = 0
    
    logger.info(f"🔄 {reason} - {stats} actives cleared, {queue_stats} file cleared, Compteurs reset")
    
    await notify_admin_reset(reason, stats, queue_stats)

# ============================================================================
# COMMANDES ADMIN (NOUVELLES COMMANDES AJOUTÉES)
# ============================================================================

# NOUVEAU: Commande /compteur1 - Voir le statut actuel du Compteur1
async def cmd_compteur1(event):
    global compteur1_trackers
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        lines = [
            "🎯 **COMPTEUR1** (Présences consécutives)",
            "Reset à 0 si le costume manque",
            ""
        ]
        
        for suit in ALL_SUITS:
            tracker = compteur1_trackers.get(suit)
            if tracker:
                if tracker.counter > 0:
                    lines.append(f"{tracker.get_display_name()}: **{tracker.counter}** consécutifs (depuis #{tracker.start_game})")
                else:
                    lines.append(f"{tracker.get_display_name()}: 0")
        
        lines.append(f"\n**Usage:** `/stats` pour voir l'historique des séries ≥3")
        
        await event.respond("\n".join(lines))
        
    except Exception as e:
        logger.error(f"Erreur cmd_compteur1: {e}")
        await event.respond(f"❌ Erreur: {e}")

# NOUVEAU: Commande /stats - Voir l'historique des séries Compteur1
async def cmd_stats(event):
    global compteur1_history, compteur1_trackers
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        lines = [
            "📊 **STATISTIQUES COMPTEUR1**",
            "Séries de présences consécutives (minimum 3)",
            ""
        ]
        
        # Sauvegarder les séries en cours avant affichage
        for tracker in compteur1_trackers.values():
            if tracker.counter >= MIN_CONSECUTIVE_FOR_STATS:
                # Vérifier si déjà sauvegardée récemment
                already_saved = False
                for entry in compteur1_history[:5]:  # Vérifier 5 dernières
                    if (entry['suit'] == tracker.suit and 
                        entry['count'] == tracker.counter and
                        entry['end_game'] == tracker.last_game):
                        already_saved = True
                        break
                
                if not already_saved:
                    save_compteur1_series(tracker.suit, tracker.counter, tracker.start_game, tracker.last_game)
        
        # Organiser par costume
        stats_by_suit = {'♥': [], '♠': [], '♦': [], '♣': []}
        for entry in compteur1_history:
            suit = entry['suit']
            if suit in stats_by_suit:
                stats_by_suit[suit].append(entry)
        
        suit_names = {
            '♥': '❤️ Cœur',
            '♠': '♠️ Pique', 
            '♦': '♦️ Carreau',
            '♣': '♣️ Trèfle'
        }
        
        has_data = False
        
        for suit in ['♥', '♠', '♦', '♣']:
            entries = stats_by_suit[suit]
            if not entries:
                continue
            
            has_data = True
            record = get_compteur1_record(suit)
            
            lines.append(f"**{suit_names[suit]}** (Record: {record})")
            
            # Afficher les 5 dernières séries
            for i, entry in enumerate(entries[:5], 1):
                count = entry['count']
                start = entry['start_game']
                end = entry['end_game']
                is_record = "⭐" if count == record else ""
                lines.append(f"  {i}. {count} fois (jeux #{start}-#{end}) {is_record}")
            
            lines.append("")
        
        if not has_data:
            lines.append("❌ Aucune série ≥3 enregistrée encore")
            lines.append("Les séries apparaîtront automatiquement quand un costume")
            lines.append("sera présent 3+ fois consécutivement.")
        
        await event.respond("\n".join(lines))
        
    except Exception as e:
        logger.error(f"Erreur cmd_stats: {e}")
        await event.respond(f"❌ Erreur: {e}")

# Commandes existantes (pause, config, etc.)
async def cmd_pause(event):
    global pause_active, pause_counter, pause_cycle_index, PAUSE_CYCLE, PREDICTIONS_BEFORE_PAUSE
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            status_pause = "🟢 ACTIVE" if pause_active else "🔴 INACTIVE"
            
            time_info = ""
            if pause_active and pause_end_time:
                remaining = int((pause_end_time - datetime.now()).total_seconds())
                if remaining > 0:
                    mins = remaining // 60
                    secs = remaining % 60
                    time_info = f"\n⏳ Temps restant: {mins}:{secs:02d}"
                else:
                    time_info = "\n⏳ Temps écoulé (devrait se terminer...)"
            
            current_duration = PAUSE_CYCLE[pause_cycle_index % len(PAUSE_CYCLE)] if not pause_active else "En cours"
            
            await event.respond(
                f"⏸️ **SYSTÈME DE PAUSE**\n\n"
                f"Statut: {status_pause}{time_info}\n\n"
                f"📊 Configuration:\n"
                f"• Cycle: {PAUSE_CYCLE} minutes\n"
                f"• Prochaine pause: {current_duration} min\n"
                f"• Prédictions avant pause: {PREDICTIONS_BEFORE_PAUSE}\n"
                f"• Compteur actuel: {pause_counter}/{PREDICTIONS_BEFORE_PAUSE}\n"
                f"• Cycle actuel: #{pause_cycle_index + 1}\n\n"
                f"**Usage:**\n"
                f"`/pause on` - Activer manuellement\n"
                f"`/pause off` - Désactiver manuellement\n"
                f"`/pausecycle 3,5,4` - Modifier le cycle\n"
                f"`/pauseadd [texte]` - Ajouter expression reprise"
            )
            return
        
        arg = parts[1].lower()
        
        if arg == 'on':
            if pause_active:
                await event.respond("⏸️ Pause déjà active")
                return
            await start_pause()
            await event.respond("✅ **Pause activée manuellement**")
            
        elif arg == 'off':
            if not pause_active:
                await event.respond("▶️ Pas de pause active")
                return
            await end_pause()
            await event.respond("✅ **Pause désactivée manuellement**")
            
        else:
            await event.respond("❌ Usage: `/pause` ou `/pause on/off`")
            
    except Exception as e:
        logger.error(f"Erreur cmd_pause: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_pausecycle(event):
    global PAUSE_CYCLE
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            cycle_text = f"🔄 **CYCLE DE PAUSE**\n\nCycle actuel: **{PAUSE_CYCLE}** minutes\n\nOrdre des pauses:\n"
            
            for i, duration in enumerate(PAUSE_CYCLE, 1):
                cycle_text += f"{i}. Pause #{i}: {duration} minutes\n"
            
            cycle_text += f"\n**Usage:** `/pausecycle 3,5,4,6` (durées en minutes, séparées par des virgules)"
            await event.respond(cycle_text)
            return
        
        arg = parts[1]
        try:
            new_cycle = [int(x.strip()) for x in arg.split(',')]
            
            if len(new_cycle) < 1:
                await event.respond("❌ Minimum 1 durée requise")
                return
            
            if any(d <= 0 or d > 60 for d in new_cycle):
                await event.respond("❌ Les durées doivent être entre 1 et 60 minutes")
                return
            
            old_cycle = PAUSE_CYCLE
            PAUSE_CYCLE = new_cycle
            
            await event.respond(
                f"✅ **Cycle modifié**\n\n"
                f"Ancien: {old_cycle}\n"
                f"Nouveau: **{PAUSE_CYCLE}**"
            )
            logger.info(f"Admin change cycle pause: {old_cycle} → {PAUSE_CYCLE}")
            
        except ValueError:
            await event.respond("❌ Format invalide. Usage: `/pausecycle 3,5,4`")
            
    except Exception as e:
        logger.error(f"Erreur cmd_pausecycle: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_pauseadd(event):
    global RESUME_EXPRESSIONS
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split(' ', 1)
        
        if len(parts) < 2:
            examples = random.sample(RESUME_EXPRESSIONS, min(5, len(RESUME_EXPRESSIONS)))
            examples_text = "\n".join([f"{i+1}. {ex[:50]}..." for i, ex in enumerate(examples)])
            
            await event.respond(
                f"📝 **EXPRESSIONS DE REPRISE**\n\n"
                f"Nombre actuel: **{len(RESUME_EXPRESSIONS)}** expressions\n\n"
                f"Exemples:\n{examples_text}\n\n"
                f"**Usage:** `/pauseadd Votre expression ici - Sossou Kouamé`"
            )
            return
        
        new_expr = parts[1].strip()
        
        if len(new_expr) < 10:
            await event.respond("❌ Expression trop courte (min 10 caractères)")
            return
        
        if len(new_expr) > 200:
            await event.respond("❌ Expression trop longue (max 200 caractères)")
            return
        
        RESUME_EXPRESSIONS.append(new_expr)
        
        await event.respond(
            f"✅ **Expression ajoutée**\n\n"
            f"Total: {len(RESUME_EXPRESSIONS)} expressions\n"
            f"Nouvelle: _{new_expr[:60]}..._"
        )
        logger.info(f"Admin ajoute expression pause: {new_expr[:50]}...")
        
    except Exception as e:
        logger.error(f"Erreur cmd_pauseadd: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_gap(event):
    global MIN_GAP_BETWEEN_PREDICTIONS
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            await event.respond(
                f"📏 **CONFIGURATION DES ÉCARTS**\n\n"
                f"Écart minimum actuel: **{MIN_GAP_BETWEEN_PREDICTIONS}** numéros\n\n"
                f"**Usage:** `/gap [2-10]`"
            )
            return
        
        arg = parts[1].lower()
        
        try:
            gap_val = int(arg)
            if not 2 <= gap_val <= 10:
                await event.respond("❌ L'écart doit être entre 2 et 10")
                return
            
            old_gap = MIN_GAP_BETWEEN_PREDICTIONS
            MIN_GAP_BETWEEN_PREDICTIONS = gap_val
            
            await event.respond(f"✅ **Écart modifié: {old_gap} → {gap_val}**")
            logger.info(f"Admin change écart: {old_gap} → {gap_val}")
            
        except ValueError:
            await event.respond("❌ Usage: `/gap [2-10]`")
            
    except Exception as e:
        logger.error(f"Erreur cmd_gap: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_canal_compteur2(event):
    global COMPTEUR2_CHANNEL_ID
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            if COMPTEUR2_CHANNEL_ID:
                await event.respond(
                    f"📊 **CANAL COMPTEUR2**\n\n"
                    f"✅ Actif: `{COMPTEUR2_CHANNEL_ID}`\n\n"
                    f"**Usage:** `/canalcompteur2 [ID]` ou `/canalcompteur2 off`"
                )
            else:
                await event.respond(
                    f"📊 **CANAL COMPTEUR2**\n\n"
                    f"❌ Inactif\n\n"
                    f"**Usage:** `/canalcompteur2 [ID]`"
                )
            return
        
        arg = parts[1].lower()
        
        if arg == 'off':
            old_id = COMPTEUR2_CHANNEL_ID
            COMPTEUR2_CHANNEL_ID = None
            await event.respond(f"❌ **Canal Compteur2 désactivé** (était: `{old_id}`)")
            logger.info(f"Admin désactive canal compteur2")
            return
        
        try:
            new_id = int(arg)
            channel_entity = await resolve_channel(new_id)
            if not channel_entity:
                await event.respond(f"❌ Canal `{new_id}` inaccessible")
                return
            
            old_id = COMPTEUR2_CHANNEL_ID
            COMPTEUR2_CHANNEL_ID = new_id
            
            await event.respond(f"✅ **Canal Compteur2: {old_id} → {new_id}**")
            logger.info(f"Admin change canal compteur2: {old_id} → {new_id}")
            
        except ValueError:
            await event.respond("❌ Usage: `/canalcompteur2 [ID]` ou `/canalcompteur2 off`")
            
    except Exception as e:
        logger.error(f"Erreur cmd_canal_compteur2: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_canaux(event):
    global COMPTEUR2_CHANNEL_ID, PREDICTION_CHANNEL_ID, SOURCE_CHANNEL_ID
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    lines = [
        "📡 **CONFIGURATION DES CANAUX**",
        "",
        f"📥 **Source:** `{SOURCE_CHANNEL_ID}`",
        f"📤 **Principal:** `{PREDICTION_CHANNEL_ID}`",
        "",
        f"📊 **Compteur2:** {f'`{COMPTEUR2_CHANNEL_ID}`' if COMPTEUR2_CHANNEL_ID else '❌'}",
    ]
    
    await event.respond("\n".join(lines))

async def cmd_queue(event):
    global prediction_queue, current_game_number, MIN_GAP_BETWEEN_PREDICTIONS, PREDICTION_SEND_AHEAD, pause_active
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        if pause_active:
            await event.respond("⏸️ **En pause** - File d'attente figée")
            return
        
        lines = [
            "📋 **FILE D'ATTENTE**",
            f"Écart: {MIN_GAP_BETWEEN_PREDICTIONS} | Envoi: N-{PREDICTION_SEND_AHEAD}",
            "",
        ]
        
        if not prediction_queue:
            lines.append("❌ Vide")
        else:
            lines.append(f"**{len(prediction_queue)} prédictions:**\n")
            
            for i, pred in enumerate(prediction_queue, 1):
                suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
                pred_type = pred['type']
                pred_num = pred['game_number']
                
                type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
                
                send_threshold = pred_num - PREDICTION_SEND_AHEAD
                
                if current_game_number >= send_threshold:
                    status = "🟢 PRÊT" if not pending_predictions else "⏳ Attente"
                else:
                    wait_num = send_threshold - current_game_number
                    status = f"⏳ Dans {wait_num}"
                
                lines.append(f"{i}. #{pred_num} {suit} | {type_str} | {status}")
        
        lines.append(f"\n🎮 Canal: #{current_game_number}")
        
        await event.respond("\n".join(lines))
        
    except Exception as e:
        logger.error(f"Erreur cmd_queue: {e}")
        await event.respond(f"❌ Erreur: {str(e)}")

async def cmd_compteur2(event):
    global compteur2_seuil_B, compteur2_active, compteur2_trackers
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            status_str = "✅ ON" if compteur2_active else "❌ OFF"
            
            lines = [
                "📊 **COMPTEUR2** (Costumes manquants)",
                f"Statut: {status_str} | Seuil B: {compteur2_seuil_B}",
                f"📺 Dernier jeu reçu: #{last_game_number_received}",
                "",
                "Progression par costume:",
            ]
            
            for suit in ALL_SUITS:
                tracker = compteur2_trackers.get(suit)
                if tracker:
                    seuil = compteur2_seuil_by_suit.get(suit, compteur2_seuil_B)
                    individuel = suit in compteur2_seuil_by_suit
                    progress = min(tracker.counter, seuil)
                    bar = f"[{'█' * progress}{'░' * (seuil - progress)}]"
                    marqueur = f"*(B={seuil})" if individuel else ""
                    
                    if tracker.counter >= seuil:
                        status = f"🔮 PRÊT {marqueur}"
                    else:
                        status = f"{tracker.counter}/{seuil} {marqueur}"
                    
                    lines.append(f"{tracker.get_display_name()}: {bar} {status.strip()}")
            
            lines.append(f"**Usage:** `/compteur2 [B/on/off/reset]`")
            
            await event.respond("\n".join(lines))
            return
        
        arg = parts[1].lower()
        
        if arg == 'off':
            compteur2_active = False
            await event.respond("❌ **Compteur2 OFF**")
        elif arg == 'on':
            compteur2_active = True
            await event.respond("✅ **Compteur2 ON**")
        elif arg == 'reset':
            for tracker in compteur2_trackers.values():
                tracker.counter = 0
            await event.respond("🔄 **Compteur2 reset**")
        else:
            try:
                b_val = int(arg)
                if not 2 <= b_val <= 10:
                    await event.respond("❌ B entre 2 et 10")
                    return
                compteur2_seuil_B = b_val
                await event.respond(f"✅ **Seuil B = {b_val}**")
            except ValueError:
                await event.respond("❌ Usage: `/compteur2 [B/on/off/reset]`")
                
    except Exception as e:
        logger.error(f"Erreur cmd_compteur2: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_compteur2b(event):
    """Définit le seuil B pour chaque costume individuellement."""
    global compteur2_seuil_by_suit, compteur2_seuil_B
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    try:
        parts = event.message.message.split()
        
        if len(parts) == 1:
            # Afficher les seuils actuels
            lines = ["📊 **SEUILS B PAR COSTUME**", ""]
            for suit in ALL_SUITS:
                tracker = compteur2_trackers.get(suit)
                if tracker:
                    seuil = compteur2_seuil_by_suit.get(suit, compteur2_seuil_B)
                    lines.append(f"{tracker.get_display_name()}: {seuil}")
            lines.append("")
            lines.append("**Usage:** `/compteur2b ♠ 2` ou `/compteur2b reset`")
            await event.respond("\n".join(lines))
            return
        
        if len(parts) == 2 and parts[1].lower() == "reset":
            compteur2_seuil_by_suit.clear()
            await event.respond("🔄 **Tous les seuils réinitialisés au seuil global**")
            return
        
        if len(parts) >= 3:
            suit_input = parts[1]
            try:
                b_val = int(parts[2])
                if not 2 <= b_val <= 10:
                    await event.respond("❌ B entre 2 et 10")
                    return
                # Trouver le costume correspondant
                found_suit = None
                for suit in ALL_SUITS:
                    if suit == suit_input or suit_input in ['pique', 'coeur', 'carreau', 'trefle', '♠', '♥', '♦', '♣']:
                        if (suit == '♠' and suit_input in ['pique', '♠']) or \
                           (suit == '♥' and suit_input in ['coeur', '❤️', '♥']) or \
                           (suit == '♦' and suit_input in ['carreau', '♦']) or \
                           (suit == '♣' and suit_input in ['trefle', '♣']):
                            found_suit = suit
                            break
                if not found_suit:
                    await event.respond("❌ Costume invalide (♠ ♥ ♦ ♣)")
                    return
                compteur2_seuil_by_suit[found_suit] = b_val
                tracker = compteur2_trackers.get(found_suit)
                if tracker:
                    await event.respond(f"✅ {tracker.get_display_name()}: B = {b_val}")
            except ValueError:
                await event.respond("❌ Usage: `/compteur2b ♠ 3` ou `/compteur2b reset`")
    except Exception as e:
        logger.error(f"Erreur cmd_compteur2b: {e}")
        await event.respond(f"❌ Erreur: {e}")

async def cmd_history(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    lines = ["📜 **HISTORIQUE**", ""]
    
    recent = prediction_history[:10]
    
    if not recent:
        lines.append("❌ Aucune prédiction")
    else:
        for i, pred in enumerate(recent, 1):
            suit = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            status = pred['status']
            pred_time = pred['predicted_at'].strftime('%H:%M:%S')
            
            rule = "📊C2" if pred.get('type') == 'compteur2' else "🤖"
            emoji = {'en_cours': '🎰', 'gagne_r0': '🏆', 'gagne_r1': '🏆', 'gagne_r2': '🏆', 'gagne_r3': '🏆', 'perdu': '💔'}.get(status, '❓')
            
            lines.append(f"{i}. {emoji} #{pred['predicted_game']} {suit} | {rule} | {status}")
            lines.append(f"   🕐 {pred_time}")
    
    await event.respond("\n".join(lines))

async def cmd_debug_groupe(event):
    """Teste la détection du premier groupe de costumes sur un message collé."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    try:
        # Utilise le texte après la commande comme message de test
        parts = event.message.message.split(None, 1)
        if len(parts) < 2:
            await event.respond(
                "🔍 **TEST DÉTECTION GROUPE**\n\n"
                "Utilisation: `/debug_groupe <texte du message>`\n\n"
                "Colle le texte d'un jeu pour voir quel premier groupe est détecté."
            )
            return
        test_msg = parts[1]
        groups = extract_parentheses_groups(test_msg)
        first_suit_group = get_first_suit_group(test_msg)
        suits_found = get_suits_in_group(first_suit_group)
        suits_missing_list = [s for s in ALL_SUITS if s not in suits_found]
        
        lines = [
            "🔍 **ANALYSE DU MESSAGE**\n",
            f"**Tous les groupes trouvés ({len(groups)}) :**"
        ]
        for i, g in enumerate(groups):
            content = g.split(':', 1)[1] if ':' in g else g
            suits_in_g = get_suits_in_group(g)
            marker = " ← **1er groupe costumes**" if g == first_suit_group else ""
            lines.append(f"  `Groupe {i+1}:` `{content[:40]}`{marker}")
            if suits_in_g:
                lines.append(f"          Costumes: {' '.join(suits_in_g)}")
        
        lines.append(f"\n✅ **Premier groupe retenu:** `{first_suit_group[:50]}`")
        lines.append(f"🃏 **Costumes PRÉSENTS:** {' '.join(suits_found) if suits_found else 'Aucun'}")
        lines.append(f"❌ **Costumes MANQUANTS:** {' '.join(suits_missing_list) if suits_missing_list else 'Aucun'}")
        
        await event.respond("\n".join(lines))
    except Exception as e:
        logger.error(f"Erreur debug_groupe: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_status(event):
    global compteur2_active, compteur2_seuil_B
    global COMPTEUR2_CHANNEL_ID, pause_active, pause_counter, PREDICTIONS_BEFORE_PAUSE, PAUSE_CYCLE
    
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    compteur2_str = "✅ ON" if compteur2_active else "❌ OFF"
    pause_str = "🟢 ACTIVE" if pause_active else "🔴 INACTIVE"
    
    now = datetime.now()
    
    lines = [
        "📊 **STATUT COMPLET**",
        "",
        f"📊 Compteur2: {compteur2_str} (B={compteur2_seuil_B})",
        f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}",
        f"⏸️ Pause: {pause_str} ({pause_counter}/{PREDICTIONS_BEFORE_PAUSE})",
        f"🔄 Cycle pause: {PAUSE_CYCLE}",
        f"📋 File: {len(prediction_queue)} | Actives: {len(pending_predictions)}",
        f"🎮 Canal: #{current_game_number}",
        "",
        f"📊 C2: {COMPTEUR2_CHANNEL_ID or '❌'}",
    ]
    
    if pending_predictions:
        lines.append("")
        lines.append("🔍 **En vérification:**")
        for game_number, pred in pending_predictions.items():
            suit_display = SUIT_DISPLAY.get(pred['suit'], pred['suit'])
            rattrapage = pred.get('rattrapage', 0)
            sent_time = pred.get('sent_time')
            age_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_str = f" ({age_sec//60}m{age_sec%60:02d}s)"
            lines.append(f"  • #{game_number} {suit_display} — R{rattrapage}{age_str}")
    
    await event.respond("\n".join(lines))


def _pdf_draw_section(c, page_w, y, title: str, numbers: list, margin=50, bottom=60) -> tuple:
    """Dessine une section de costume dans le PDF avec pagination automatique."""
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.lib.pagesizes import letter
    
    line_h = 14
    max_w = page_w - margin * 2  # largeur utilisable
    
    # Titre de la section
    if y < bottom + 40:
        c.showPage()
        y = 750
    c.setFont("Helvetica-Bold", 12)
    c.drawString(margin, y, title)
    y -= 18
    
    if not numbers:
        c.setFont("Helvetica-Oblique", 10)
        c.drawString(margin + 10, y, "Aucun")
        y -= line_h
        return y
    
    # Construire les tokens (#n, #n, ...)
    tokens = [f"#{n}" for n in sorted(numbers)]
    c.setFont("Helvetica", 10)
    
    line_buf = []
    line_w = 0
    
    for tok in tokens:
        tok_w = c.stringWidth(tok + ", ", "Helvetica", 10)
        if line_w + tok_w > max_w and line_buf:
            line_text = ", ".join(line_buf)
            if y < bottom:
                c.showPage()
                y = 750
                c.setFont("Helvetica", 10)
            c.drawString(margin + 10, y, line_text)
            y -= line_h
            line_buf = [tok]
            line_w = tok_w
        else:
            line_buf.append(tok)
            line_w += tok_w
    
    if line_buf:
        if y < bottom:
            c.showPage()
            y = 750
            c.setFont("Helvetica", 10)
        c.drawString(margin + 10, y, ", ".join(line_buf))
        y -= line_h
    
    y -= 10  # espace entre sections
    return y


def generate_suits_pdf() -> str:
    """Génère un PDF avec les numéros de jeux par costume reçu. Retourne le chemin du fichier."""
    import tempfile
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.lib.pagesizes import letter
    
    tmp = tempfile.NamedTemporaryFile(suffix=".pdf", delete=False)
    tmp.close()
    path = tmp.name
    
    page_w, page_h = letter
    c = pdf_canvas.Canvas(path, pagesize=letter)
    c.setTitle("Costumes Recus 1-1440")
    
    y = page_h - 50
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, y, "COSTUMES RECUS - Jeux 1 a 1440")
    y -= 10
    c.setLineWidth(1)
    c.line(50, y, page_w - 50, y)
    y -= 25
    
    suits_info = [
        ('♠', 'PIQUE'),
        ('♥', 'COEUR'),
        ('♦', 'CARREAU'),
        ('♣', 'TREFLE'),
    ]
    
    for suit, label in suits_info:
        numbers = suits_received.get(suit, [])
        title = f"{label} ({len(numbers)} jeux)"
        y = _pdf_draw_section(c, page_w, y, title, numbers)
    
    c.save()
    return path


def generate_missing_pdf() -> str:
    """Génère un PDF avec les numéros manquants par costume. Retourne le chemin du fichier."""
    import tempfile
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.lib.pagesizes import letter
    
    tmp = tempfile.NamedTemporaryFile(suffix=".pdf", delete=False)
    tmp.close()
    path = tmp.name
    
    page_w, page_h = letter
    c = pdf_canvas.Canvas(path, pagesize=letter)
    c.setTitle("Costumes Manquants 1-1440")
    
    y = page_h - 50
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, y, "COSTUMES MANQUANTS - Jeux 1 a 1440")
    y -= 10
    c.setLineWidth(1)
    c.line(50, y, page_w - 50, y)
    y -= 25
    
    suits_info = [
        ('♠', 'PIQUE manquant'),
        ('♥', 'COEUR manquant'),
        ('♦', 'CARREAU manquant'),
        ('♣', 'TREFLE manquant'),
    ]
    
    for suit, label in suits_info:
        numbers = suits_missing.get(suit, [])
        title = f"{label} ({len(numbers)} absences)"
        y = _pdf_draw_section(c, page_w, y, title, numbers)
    
    c.save()
    return path


def _pdf_draw_outcomes_section(c, page_w, y, title: str, items: list,
                               margin=50, bottom=60, line_h=14) -> float:
    """Dessine une section outcomes (PERDU ou R3) en format 'game:emoji'."""
    if y < bottom + 40:
        c.showPage()
        y = 750
    c.setFont("Helvetica-Bold", 12)
    c.drawString(margin, y, title)
    y -= 18

    if not items:
        c.setFont("Helvetica-Oblique", 10)
        c.drawString(margin + 10, y, "Aucun")
        y -= line_h
        return y

    suit_emoji = {'♠': '♠', '♥': '♥', '♦': '♦', '♣': '♣'}
    max_w = page_w - margin * 2
    tokens = [f"{it['game']}:{suit_emoji.get(it['suit'], it['suit'])}" for it in items]

    c.setFont("Helvetica", 10)
    line_buf = []
    line_w = 0
    for tok in tokens:
        tok_w = c.stringWidth(tok + "  ", "Helvetica", 10)
        if line_w + tok_w > max_w and line_buf:
            line_text = "  ".join(line_buf)
            if y < bottom:
                c.showPage()
                y = 750
                c.setFont("Helvetica", 10)
            c.drawString(margin + 10, y, line_text)
            y -= line_h
            line_buf = [tok]
            line_w = tok_w
        else:
            line_buf.append(tok)
            line_w += tok_w

    if line_buf:
        if y < bottom:
            c.showPage()
            y = 750
            c.setFont("Helvetica", 10)
        c.drawString(margin + 10, y, "  ".join(line_buf))
        y -= line_h

    y -= 10
    return y


def generate_outcomes_pdf() -> str:
    """Génère un PDF avec les résultats PERDU et R3 GAGNÉ. Format: 'game:suit'."""
    import tempfile
    from reportlab.pdfgen import canvas as pdf_canvas
    from reportlab.lib.pagesizes import letter

    tmp = tempfile.NamedTemporaryFile(suffix=".pdf", delete=False)
    tmp.close()
    path = tmp.name

    page_w, page_h = letter
    c = pdf_canvas.Canvas(path, pagesize=letter)
    c.setTitle("Resultats PERDU et R3 1-1440")

    y = page_h - 50
    c.setFont("Helvetica-Bold", 16)
    c.drawString(50, y, "RESULTATS PERDU / R3 GAGNE - Jeux 1 a 1440")
    y -= 10
    c.setLineWidth(1)
    c.line(50, y, page_w - 50, y)
    y -= 25

    y = _pdf_draw_outcomes_section(
        c, page_w, y,
        f"PERDU ({len(predictions_lost)} predictions)",
        predictions_lost
    )
    y = _pdf_draw_outcomes_section(
        c, page_w, y,
        f"R3 GAGNE ({len(predictions_r3)} predictions)",
        predictions_r3
    )

    c.save()
    return path


async def send_pdfs_to_admin():
    """Envoie les deux PDFs au chat privé de l'admin."""
    import os as _os
    try:
        path1 = generate_suits_pdf()
        path2 = generate_missing_pdf()
        path3 = generate_outcomes_pdf()
        await client.send_file(
            ADMIN_ID, path1,
            caption="📊 Costumes RECUS (1-1440)",
            file_name="costumes_recus.pdf",
            force_document=True
        )
        await client.send_file(
            ADMIN_ID, path2,
            caption="📊 Costumes MANQUANTS (1-1440)",
            file_name="costumes_manquants.pdf",
            force_document=True
        )
        await client.send_file(
            ADMIN_ID, path3,
            caption="📊 Résultats PERDU / R3 GAGNÉ (1-1440)",
            file_name="resultats_perdu_r3.pdf",
            force_document=True
        )
        logger.info("✅ PDFs envoyés à l'admin")
        try:
            _os.remove(path1)
            _os.remove(path2)
            _os.remove(path3)
        except Exception:
            pass
    except Exception as e:
        logger.error(f"Erreur envoi PDFs auto: {e}")


async def cmd_export_pdf(event):
    """Exporte les PDFs des costumes reçus et manquants."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    import os as _os
    try:
        await event.respond("📄 Génération des PDFs en cours...")
        path1 = generate_suits_pdf()
        path2 = generate_missing_pdf()
        path3 = generate_outcomes_pdf()
        await event.client.send_file(
            event.sender_id, path1,
            caption="📊 Costumes RECUS (1-1440)",
            file_name="costumes_recus.pdf",
            force_document=True
        )
        await event.client.send_file(
            event.sender_id, path2,
            caption="📊 Costumes MANQUANTS (1-1440)",
            file_name="costumes_manquants.pdf",
            force_document=True
        )
        await event.client.send_file(
            event.sender_id, path3,
            caption="📊 Résultats PERDU / R3 GAGNÉ (1-1440)",
            file_name="resultats_perdu_r3.pdf",
            force_document=True
        )
        await event.respond("✅ PDFs envoyés !")
        try:
            _os.remove(path1)
            _os.remove(path2)
            _os.remove(path3)
        except Exception:
            pass
    except Exception as e:
        logger.error(f"Erreur export PDF: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_help(event):
    if event.is_group or event.is_channel:
        return
    
    help_text = f"""📖 **BACCARAT AI - COMMANDES**

**⚙️ Configuration:**
`/gap [2-10]` - Écart min entre prédictions ({MIN_GAP_BETWEEN_PREDICTIONS})

**📊 Compteur2 (costumes manquants):**
`/compteur2` - Voir état du Compteur2
`/compteur2 [B]` - Changer seuil global (ex: `/compteur2 3`)
`/compteur2 on/off` - Activer/désactiver
`/compteur2 reset` - Remettre compteurs à 0
`/compteur2b ♠ [B]` - Seuil B individuel pour ♠
`/compteur2b ♥ [B]` - Seuil B individuel pour ♥
`/compteur2b ♦ [B]` - Seuil B individuel pour ♦
`/compteur2b ♣ [B]` - Seuil B individuel pour ♣
`/compteur2b reset` - Supprimer tous les seuils individuels
`/compteur2b` - Voir les seuils actuels par costume

**📊 Compteur1 (présences consécutives):**
`/compteur1` - Voir Compteur1
`/stats` - Historique séries ≥3

**📡 Canaux:**
`/canalcompteur2 [ID/off]` - Canal dédié Compteur2
`/canaux` - Voir config canaux

**⏸️ Pause:**
`/pause [on/off]` - Gérer pause
`/pausecycle [3,5,4]` - Modifier cycle de pause
`/pauseadd [texte]` - Ajouter expression de reprise

**📋 Gestion:**
`/pending` - Prédictions en cours
`/queue` - File d'attente
`/status` - Statut complet
`/history` - Historique
`/export_pdf` - Exporter PDF costumes
`/debug_groupe [texte]` - Tester détection du 1er groupe
`/reset` - Reset complet

🤖 Baccarat AI | By Sossou Kouamé"""
    
    await event.respond(help_text)

async def cmd_pending(event):
    """Affiche les prédictions en cours de vérification."""
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    from config import PREDICTION_TIMEOUT_MINUTES
    now = datetime.now()
    
    try:
        if not pending_predictions:
            await event.respond("✅ **Aucune prédiction en cours**\n\nLe bot est prêt à envoyer la prochaine.")
            return
        
        lines = [
            f"🔍 **PRÉDICTIONS EN COURS** ({len(pending_predictions)})",
            ""
        ]
        
        for game_number, pred in pending_predictions.items():
            suit = pred.get('suit', '?')
            suit_display = SUIT_DISPLAY.get(suit, suit)
            rattrapage = pred.get('rattrapage', 0)
            current_check = pred.get('current_check', game_number)
            verified_games = pred.get('verified_games', [])
            sent_time = pred.get('sent_time')
            pred_type = pred.get('type', 'standard')
            
            type_str = "📊C2" if pred_type == 'compteur2' else "🤖"
            
            age_str = ""
            timeout_str = ""
            if sent_time:
                age_sec = int((now - sent_time).total_seconds())
                age_min = age_sec // 60
                age_sec_r = age_sec % 60
                age_str = f"{age_min}m{age_sec_r:02d}s"
                remaining_min = PREDICTION_TIMEOUT_MINUTES - age_min
                timeout_str = f" | Timeout: {remaining_min}min"
            
            verif_parts = []
            for i in range(4):
                check_num = game_number + i
                if current_check == check_num:
                    verif_parts.append(f"🔵#{check_num}")
                elif check_num in verified_games:
                    verif_parts.append(f"❌#{check_num}")
                else:
                    verif_parts.append(f"⬜#{check_num}")
            
            lines.append(f"**#{game_number}** {suit_display} | {type_str} | R{rattrapage}")
            lines.append(f"  🔍 {' | '.join(verif_parts)}")
            lines.append(f"  ⏱️ Envoyé il y a {age_str}{timeout_str}")
            lines.append("")
        
        lines.append(f"🎮 Canal source: #{current_game_number}")
        
        await event.respond("\n".join(lines))
        
    except Exception as e:
        logger.error(f"Erreur cmd_pending: {e}")
        await event.respond(f"❌ Erreur: {e}")


async def cmd_reset(event):
    if event.is_group or event.is_channel:
        return
    if event.sender_id != ADMIN_ID and ADMIN_ID != 0:
        await event.respond("🔒 Admin uniquement")
        return
    
    await event.respond("🔄 Reset...")
    await perform_full_reset("Reset manuel")
    await event.respond("✅ Reset effectué!")

# ============================================================================
# SETUP ET DÉMARRAGE
# ============================================================================

def setup_handlers():
    # Configuration
    client.add_event_handler(cmd_gap, events.NewMessage(pattern=r'^/gap'))
    
    # Canaux
    client.add_event_handler(cmd_canal_compteur2, events.NewMessage(pattern=r'^/canalcompteur2'))
    client.add_event_handler(cmd_canaux, events.NewMessage(pattern=r'^/canaux$'))
    
    # Pause
    client.add_event_handler(cmd_pause, events.NewMessage(pattern=r'^/pause'))
    client.add_event_handler(cmd_pausecycle, events.NewMessage(pattern=r'^/pausecycle'))
    client.add_event_handler(cmd_pauseadd, events.NewMessage(pattern=r'^/pauseadd'))
    
    # NOUVEAU: Compteurs et stats
    client.add_event_handler(cmd_compteur1, events.NewMessage(pattern=r'^/compteur1$'))
    client.add_event_handler(cmd_stats, events.NewMessage(pattern=r'^/stats$'))
    
    # Gestion
    client.add_event_handler(cmd_queue, events.NewMessage(pattern=r'^/queue$'))
    client.add_event_handler(cmd_pending, events.NewMessage(pattern=r'^/pending$'))
    client.add_event_handler(cmd_compteur2, events.NewMessage(pattern=r'^/compteur2($|\s)'))
    client.add_event_handler(cmd_compteur2b, events.NewMessage(pattern=r'^/compteur2b'))
    client.add_event_handler(cmd_debug_groupe, events.NewMessage(pattern=r'^/debug_groupe'))
    client.add_event_handler(cmd_export_pdf, events.NewMessage(pattern=r'^/export_pdf$'))
    client.add_event_handler(cmd_status, events.NewMessage(pattern=r'^/status$'))
    client.add_event_handler(cmd_history, events.NewMessage(pattern=r'^/history$'))
    client.add_event_handler(cmd_reset, events.NewMessage(pattern=r'^/reset$'))
    client.add_event_handler(cmd_help, events.NewMessage(pattern=r'^/help$'))
    
    # Messages
    client.add_event_handler(handle_new_message, events.NewMessage())
    client.add_event_handler(handle_edited_message, events.MessageEdited())

async def start_bot():
    global client, prediction_channel_ok
    
    session = os.getenv('TELEGRAM_SESSION', '')
    client = TelegramClient(StringSession(session), API_ID, API_HASH)
    
    try:
        await client.start(bot_token=BOT_TOKEN)
        setup_handlers()
        initialize_trackers()
        
        if PREDICTION_CHANNEL_ID:
            try:
                pred_entity = await resolve_channel(PREDICTION_CHANNEL_ID)
                if pred_entity:
                    prediction_channel_ok = True
                    logger.info(f"✅ Canal prédiction OK")
            except Exception as e:
                logger.error(f"❌ Erreur canal prédiction: {e}")
        
        logger.info("🤖 Bot démarré")
        return True
        
    except Exception as e:
        logger.error(f"❌ Erreur démarrage: {e}")
        return False

async def main():
    try:
        if not await start_bot():
            return
        
        asyncio.create_task(auto_reset_system())
        asyncio.create_task(reaction_update_task())
        
        app = web.Application()
        app.router.add_get('/health', lambda r: web.Response(text="OK"))
        app.router.add_get('/', lambda r: web.Response(text="BACCARAT AI 🤖 Running"))
        
        runner = web.AppRunner(app)
        await runner.setup()
        
        site = web.TCPSite(runner, '0.0.0.0', PORT)
        await site.start()
        
        logger.info(f"🌐 Web server port {PORT}")
        logger.info(f"📏 Écart: {MIN_GAP_BETWEEN_PREDICTIONS}")
        logger.info(f"⏸️ Pause cycle: {PAUSE_CYCLE} min")
        logger.info(f"📊 Compteur2: ACTIVE (B={compteur2_seuil_B})")
        logger.info(f"🎯 Compteur1 (présences): ACTIVE")
        logger.info(f"✅ Système de pause corrigé")
        
        await client.run_until_disconnected()
        
    except Exception as e:
        logger.error(f"❌ Erreur main: {e}")
    finally:
        if client and client.is_connected():
            await client.disconnect()

if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Arrêté")
    except Exception as e:
        logger.error(f"Fatal: {e}")
        sys.exit(1)
