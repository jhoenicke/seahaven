const ytop = 10; 

const xoffset = 10;
const xgrid = 150;
const yoffset = 220;
const ygrid = 40;

var pos2card = new Uint8Array(52);
var stacks = new Uint8Array(10);
var spots = new Uint8Array(4);
var flutes = new Uint8Array(10);
var aces = new Uint8Array(4);
var kings = new Uint8Array(4);
var svg;

// Levels of automation.  Every level includes the previous ones.
const AUTO_NONE = 0;   // move single cards only, no automatic moves at all
const AUTO_FLUTE = 1;  // move whole flutes (or as much of it as the cells hold)
const AUTO_ACES = 2;   // ... and move cards to the foundations automatically
const AUTO_FULL = 3;   // ... and move cards from the cells back to the piles
const AUTO_LEVELS = 4;

// destinations that are not a column
const DEST_ACES = -2;
const DEST_CELL = -1;

// Every entry of the move log is a single card move, given by the place the
// card is taken from; the destination is the one a click without automation
// chooses.  The marker of an entry tells from which automation level on the
// move is made without being clicked, so undo can skip all moves that the
// current level makes by itself.
const MARK_FLUTE = AUTO_FLUTE;   // one card of a flute that is moved at once
const MARK_ACES = AUTO_ACES;     // move to the foundations
const MARK_CELL = AUTO_FULL;     // move from a cell to a pile
const MARK_CLICK = AUTO_LEVELS;  // a move no level makes: never skipped

// The automation level is a setting, not a move.  Changing it may make the
// moves that are automatic on the new level, but those are logged like any
// other move; the level itself is not part of the log.
var automation = AUTO_FULL;

// while replaying stored moves they are not appended to the log again
var recording = true;

// New games can be taken back as well: the last MAX_GAMES games are kept,
// each with its own move log.
const MAX_GAMES = 5;
var games = [];
var gameIndex = 0;

var highlightedCard = 0;
var undoLog = [];
var moves = [];

var solver = null;
var isChecking = false;

// With this setting a new game is dealt again until the solver says that it
// can be won.  While it looks for one, isSearching is set and the answer to
// the question solverRequest decides whether the deal is kept.
var ensureSolvable = false;
var isSearching = false;
var solverRequest = 0;

function shuffle(array) {
    var current, temp, random;
    
    // While there remain elements to shuffle...
    for (current = array.length - 1; current > 0; current--) {

        // Pick a random element up to (and including) current...
        random = Math.floor(Math.random() * (current + 1));
        
        // And swap it with the current element.
        temp = array[current];
        array[current] = array[random];
        array[random] = temp;
    }
    return array;
}

function card2html(card, x, y) {
    var html = '<use x="' + x + '" y="' +y +
            '" width="130" height="182" href="#c' + card + '" />';
    if (card == highlightedCard) {
        html += '<use x="' + x + '" y="' +y +
            '" width="130" height="182" href="#hl" />';
    }
    return html;
}

function storeGames() {
    games[gameIndex] = currentGame();
    window.localStorage.setItem("seahavenGames", JSON.stringify(games));
    window.localStorage.setItem("seahavenGameIndex", JSON.stringify(gameIndex));
    window.localStorage.setItem("seahavenAutomation", JSON.stringify(automation));
    window.localStorage.setItem("seahavenEnsureSolvable",
                                JSON.stringify(ensureSolvable));
}

// A move is stored as [source, marker].  Games stored by an older version
// contain the clicked column alone; they are converted when they are loaded.
function sourceOf(entry) {
    return entry[0];
}

function markerOf(entry) {
    return entry[1];
}

function isOldFormat(log) {
    return log.length > 0 && !Array.isArray(log[0]);
}

// remember one card move; during replay the log already has the entry
function logMove(src, marker) {
    if (recording) {
        while (moves.length > numMoves) {
            moves.pop();
        }
        moves.push([src, marker]);
    }
    numMoves++;
}

function computeFluteDist(col) {
    return Math.min(ygrid, (435 - (stacks[col] - 1) * ygrid) / flutes[col]);
}

function updateBoard() {
    var cardContainer = document.getElementById("cards");
    var html = "";
    for (var suit = 0; suit < 4; suit++) {
        if (aces[suit] > 0) {
            var card = suit * 13 + aces[suit];
            var col = suit < 2 ? suit : suit + 6;
            html += card2html(card, xoffset + col * xgrid, ytop);
        }
    }
    for (var col = 0; col < 4; col++) {
        if (spots[col] > 0) {
            html += card2html(spots[col], xoffset + (col + 3) * xgrid, ytop);
        }
    }
    for (var col = 0; col < 10; col++) {
        for (var d = 0; d < stacks[col]; d++) {
            var card = pos2card[10 * d + col];
            html += card2html(card, xoffset + col * xgrid, yoffset + d * ygrid);
            if (d == stacks[col] - 1) {
                var yflute = computeFluteDist(col);
                for (var f = 0; f < flutes[col]; f++) {
                    card--;
                    html += card2html(card, xoffset + col * xgrid, yoffset + d * ygrid + (1 + f) * yflute);
                }
            }
        }
    }
    for (var i = 0; i < 4; i++) {
        if (kings[i] > 0) {
            var col = kings[i] % 10;
            var flutelen = Math.floor(kings[i] / 10);
            var card = i*13+13;
            for (var f = 0; f < flutelen; f++) {
                html += card2html(card, xoffset + col * xgrid, yoffset + f * ygrid);
                card--;
            }
        }
    }
    cardContainer.innerHTML = html;
    updateOptionsBox();
}

// the row of a setting is bright while the setting is on
function markRow(id, on) {
    var row = document.getElementById(id);
    if (row) {
        row.style.fill = on ? "#fff" : "#000";
        row.style.fillOpacity = on ? 0.35 : 0.15;
    }
}

function updateOptionsBox() {
    for (var level = 0; level < AUTO_LEVELS; level++) {
        markRow("auto" + level, level == automation);
    }
    markRow("ensure", ensureSolvable);
    markRow("fullscreen", isFullscreen());
}

function optionsOpen() {
    return document.getElementById("optionsbox").style.visibility == "visible";
}

function toggleOptions() {
    document.getElementById("optionsbox").style.visibility =
        optionsOpen() ? "hidden" : "visible";
}

function hideOptions() {
    if (optionsOpen()) {
        document.getElementById("optionsbox").style.visibility = "hidden";
        return true;
    }
    return false;
}

function gameOver() {
    for (var suit = 0; suit < 4; suit++) {
        if (aces[suit] != 13) {
            return false;
        }
    }
    return true;
}

function countEmptySpots() {
    var empty = 0;
    spots.forEach(spot => { if (spot == 0) { empty++ }; });
    return empty;
}

function addSpot(card) {
    for (var i = 0; i < 4; i++) {
        if (spots[i] == 0) {
            spots[i] = card;
            return;
        }
    }
    throw ("No space for " + card + " ???");
}

function getSnapshot(srccol) {
    return {
        "stacks" : [...stacks],
        "flutes" : [...flutes],
        "spots" : [...spots],
        "aces" : [...aces],
        "kings": [...kings],
        "srccol": srccol
    };
}

function restoreSnapshot(snap) {
    stacks = snap.stacks;
    flutes = snap.flutes;
    spots = snap.spots;
    aces = snap.aces;
    kings = snap.kings;
}

function findFreeColumn() {
    for (var i = 0; i < 10; i++) {
        if (stacks[i] == 0) {
            var foundKing = false;
            for (var j = 0; j < 4; j++) {
                if (kings[j] > 0 && kings[j] % 10 == i) {
                    foundKing = true;
                    break;
                }
            }
            if (!foundKing) {
                return i;
            }
        }
    }
    return -1;
}

/*
 * The card that a click on src would move: src is the pile 0..9 or the cell
 * -src-1.  Returns 0 if there is no card to move.
 */
function cardAt(src) {
    if (src < 0) {
        return spots[-src - 1];
    }
    if (stacks[src] > 0) {
        return pos2card[10 * (stacks[src] - 1) + src] - flutes[src];
    }
    for (var suit = 0; suit < 4; suit++) {
        if (kings[suit] > 0 && (kings[suit] % 10) == src) {
            return 13 * suit + 14 - Math.floor(kings[suit] / 10);
        }
    }
    return 0;
}

/*
 * The number of cards of the flute that ends at the bottom of src.
 */
function fluteAt(src) {
    if (stacks[src] > 0) {
        return flutes[src] + 1;
    }
    for (var suit = 0; suit < 4; suit++) {
        if (kings[suit] > 0 && (kings[suit] % 10) == src) {
            return Math.floor(kings[suit] / 10);
        }
    }
    return 0;
}

/*
 * The cell that holds the given card, as a move source.
 */
function cellOf(card) {
    for (var i = 0; i < 4; i++) {
        if (spots[i] == card) {
            return -i - 1;
        }
    }
    return 0;
}

/*
 * Find the destination for the flute of srcflute cards ending in srccard.
 * The destination is the foundation, a column, or the free cells in that
 * order, whatever is feasible.  The space in the cells is not checked here.
 */
function findDestination(srccol, srccard, srcflute) {
    var suit = Math.floor((srccard - 1) / 13);
    if (aces[suit] + 1 == srccard - srcflute + 1 - 13 * suit) {
        return DEST_ACES;
    }
    if ((srccard % 13) == 0) {
        // A king can only be moved to an empty column, and only if its own
        // column holds more than the king; otherwise nothing would be gained.
        if ((srccol < 0 || stacks[srccol] > 1) && findFreeColumn() >= 0) {
            return 10 + suit;
        }
    } else if (srccard - 13 * suit + Math.floor(kings[suit] / 10) == 13) {
        return 10 + suit;
    } else {
        for (var col = 0; col < 10; col++) {
            if (stacks[col] > 0) {
                var d = stacks[col] - 1;
                var destcard = pos2card[10*d + col] - flutes[col];
                if (srccard + 1 == destcard) {
                    return col;
                }
            }
        }
    }
    return DEST_CELL;
}

/*
 * Merging the flute of a pile and moving a lone king to the kings area do not
 * move a card on the board, they only change the internal representation, so
 * they are not logged.  This runs after every single card move.
 */
function normalize() {
    for (var col = 0; col < 10; col++) {
        while (stacks[col] > 1) {
            var d = stacks[col] - 2;
            var precard = pos2card[10*d + col];
            var card = pos2card[10*(d+1) + col];
            if (card + 1 == precard && card % 13 != 0) {
                stacks[col]--;
                flutes[col]++;
            } else {
                break;
            }
        }
        if (stacks[col] == 1) {
            var bottom = pos2card[col] - flutes[col];
            if ((bottom % 13) == 0) {
                // the column holds nothing but a king
                kings[Math.floor((bottom - 1) / 13)] = (1 + flutes[col]) * 10 + col;
                stacks[col] = 0;
                flutes[col] = 0;
            }
        }
    }
}

/*
 * The automation level from which on the given move is made without being
 * clicked: a move to the foundations from AUTO_ACES on, a move of a card that
 * is not a king from a cell back to a pile from AUTO_FULL on.
 */
function autoLevelOf(src, card, dest) {
    if (dest == DEST_ACES) {
        return MARK_ACES;
    }
    if (src < 0 && dest >= 0 && (card % 13) != 0) {
        return MARK_CELL;
    }
    return MARK_CLICK;
}

/*
 * Move the single card at src to the destination that a click without
 * automation chooses and put it into the log.  The marker tells from which
 * automation level on this move is made without being clicked.
 */
function moveCard(src, marker) {
    var card = cardAt(src);
    if (card == 0) {
        return false;
    }
    var dest = findDestination(src, card, 1);
    if (dest == DEST_CELL && (src < 0 || countEmptySpots() == 0)) {
        // moving a card from one cell to another gains nothing
        return false;
    }
    var suit = Math.floor((card - 1) / 13);

    // A clicked move that a higher level makes by itself gets the marker of
    // that level, so undo takes it back together with the move that caused it
    // instead of leaving a state the automation would run away from.
    marker = Math.min(marker, autoLevelOf(src, card, dest));

    undoLog.push(getSnapshot(src));
    logMove(src, marker);

    if (src < 0) {
        spots[-src - 1] = 0;
    } else if (stacks[src] > 0) {
        if (flutes[src] > 0) {
            flutes[src]--;
        } else {
            stacks[src]--;
        }
    } else {
        // the card is taken from the kings column
        kings[suit] -= 10;
        if (kings[suit] < 10) {
            // the king itself was moved, the column is free again
            kings[suit] = 0;
        }
    }

    if (dest == DEST_ACES) {
        aces[suit]++;
    } else if (dest == DEST_CELL) {
        addSpot(card);
    } else if (dest < 10) {
        flutes[dest]++;
    } else {
        var destsuit = dest - 10;
        if (kings[destsuit] == 0) {
            kings[destsuit] = findFreeColumn();
        }
        kings[destsuit] += 10;
    }

    normalize();
    return true;
}

/*
 * Whether the card is the next one its foundation takes.
 */
function isFoundationCard(card) {
    var suit = Math.floor((card - 1) / 13);
    return card > 0 && aces[suit] + 1 == card - 13 * suit;
}

/*
 * Make all moves that the current automation level makes by itself.  They go
 * into the log like clicked moves, with a marker that lets undo skip them.
 *
 * The foundations are served first, until no card fits on them any more.
 * Only then are the cells put back on the piles: such a move covers the card
 * it is put on and uncovers none, and the card itself does not fit on a
 * foundation or it would have gone there, so it cannot make a new foundation
 * move possible and the foundations need not be looked at again.  It can
 * however uncover the next cell card, so it needs a loop of its own.
 */
function automove() {
    var stable;
    if (automation >= AUTO_ACES) {
        stable = false;
        while (!stable) {
            stable = true;
            for (var i = 0; i < 4; i++) {
                if (isFoundationCard(spots[i])) {
                    moveCard(-i - 1, MARK_ACES);
                    stable = false;
                }
            }
            for (var col = 0; col < 10; col++) {
                if (isFoundationCard(cardAt(col))) {
                    moveCard(col, MARK_ACES);
                    stable = false;
                }
            }
        }
    }
    if (automation >= AUTO_FULL) {
        stable = false;
        while (!stable) {
            stable = true;
            for (var i = 0; i < 4; i++) {
                var card = spots[i];
                if (card > 0 && (card % 13) != 0 &&
                    findDestination(-i - 1, card, 1) >= 0) {
                    moveCard(-i - 1, MARK_CELL);
                    stable = false;
                }
            }
        }
    }
}

/*
 * Move the cards that a click on src moves on the current automation level.
 * A flute is moved card by card: the cards below its head are parked in the
 * cells, the head is moved to the destination, and the parked cards are put
 * back on top of it.
 */
function clickSource(src) {
    var card = cardAt(src);
    if (card == 0) {
        return false;
    }
    var count = (src < 0 || automation == AUTO_NONE) ? 1 : fluteAt(src);
    var extra = countEmptySpots();
    var destcol = findDestination(src, card + count - 1, count);
    if (destcol == DEST_CELL && src < 0) {
        return false;
    }

    // moving to the foundation needs no free cell, moving to a column needs
    // one free cell for every card but the last one.
    if (destcol != DEST_ACES &&
        count > (destcol == DEST_CELL ? extra : extra + 1)) {
        // The whole flute does not fit; move as many cards to the cells as
        // they can hold.  With full automation these cards would immediately
        // be moved back, without automation there is only one card anyway.
        if (extra == 0 || automation == AUTO_NONE || automation == AUTO_FULL) {
            return false;
        }
        count = extra;
        destcol = DEST_CELL;
    }

    if (destcol == DEST_ACES || destcol == DEST_CELL) {
        for (var i = 0; i < count; i++) {
            moveCard(src, i == 0 ? MARK_CLICK : MARK_FLUTE);
        }
    } else {
        var parked = [];
        for (var i = 0; i < count - 1; i++) {
            parked.push(card + i);
            moveCard(src, i == 0 ? MARK_CLICK : MARK_FLUTE);
        }
        moveCard(src, count == 1 ? MARK_CLICK : MARK_FLUTE);
        while (parked.length > 0) {
            moveCard(cellOf(parked.pop()), MARK_FLUTE);
        }
    }

    automove();
    return true;
}

function setAutomation(level) {
    automation = level;
    // a higher level makes the moves that are automatic from now on
    automove();
    storeGames();
    checkSolvable();
    updateBoard();
}

function shuffleCards() {
    for (var i = 0; i < 52; i++) {
        pos2card[i] = i+1;
    }
    shuffle(pos2card);
}

// the game that is currently on the board
function currentGame() {
    return {
        "shuffle": Array.from(pos2card),
        "moves": moves,
        "numMoves": numMoves
    };
}

// put a game of the game list on the board
function loadGame(index) {
    gameIndex = index;
    pos2card.set(games[index].shuffle);
    moves = games[index].moves;
    numMoves = games[index].numMoves;
    reset();
}

// Deal the cards of the current game again.  With the "ensure solvable"
// setting the solver is asked whether the deal can be won; its answer arrives
// while the cogwheels turn and deals again if the game has no solution.
function dealGame() {
    shuffleCards();
    moves = [];
    numMoves = 0;
    games[gameIndex] = currentGame();
    isSearching = ensureSolvable && solver !== null;
    reset();
    storeGames();
}

function newGame() {
    // the games that were taken back with undo are replaced by the new one
    games[gameIndex] = currentGame();
    games.length = gameIndex + 1;

    games.push({"shuffle": [], "moves": [], "numMoves": 0});
    gameIndex = games.length - 1;
    while (games.length > MAX_GAMES) {
        // only the last games can be taken back
        games.shift();
        gameIndex--;
    }
    // the empty game is filled with the cards of the new deal
    dealGame();
}

function reset() {
    var stored = moves;
    var target = numMoves;
    if (solver) {
        console.log("initcard: " + pos2card);
        solver.postMessage({funcName:"initcard", data: pos2card})
    }
    undoLog = [];
    moves = [];
    numMoves = 0;
    flutes.fill(0);
    stacks.fill(5);
    kings.fill(0);
    aces.fill(0);
    spots.fill(0);
    spots[1] = pos2card[50];
    spots[2] = pos2card[51];
    normalize();

    if (isOldFormat(stored)) {
        // An older version stored the clicked columns of a fully automatic
        // game.  Play them again to get the moves of every single card; the
        // moves that were undone at the time are lost.
        var setting = automation;
        automation = AUTO_FULL;
        automove();
        for (var i = 0; i < target; i++) {
            clickSource(stored[i]);
        }
        automation = setting;
        storeGames();
    } else {
        // the automatic moves of the deal are in the log like all the others
        moves = stored;
        recording = false;
        for (var i = 0; i < target; i++) {
            if (!moveCard(sourceOf(stored[i]), markerOf(stored[i]))) {
                break;
            }
        }
        recording = true;
        if (moves.length == 0) {
            // a new game: the deal itself may already move some cards
            automove();
        }
    }
    checkSolvable();
    updateBoard();
}

function makeMove(src) {
    if (clickSource(src)) {
        storeGames();
        checkSolvable();
        updateBoard();
    }
}

function clickboard(evt) {
    if (hideOptions()) {
        // the click that closes the option box does nothing else
        return;
    }
    var pt = svg.createSVGPoint()
    pt.x = evt.clientX;
    pt.y = evt.clientY;

    // The cursor point, translated into svg coordinates
    var cursorpt =  pt.matrixTransform(svg.getScreenCTM().inverse());

    var col = Math.floor((cursorpt.x-xoffset/2)/xgrid);
    if (cursorpt.y > 220 && cursorpt.y < 845 && col >= 0 && col < 10) {
        makeMove(col);
    }
    if (cursorpt.y > 10 && cursorpt.y < 200 && col >= 3 && col < 7) {
        makeMove(- (col - 3) - 1);
    }
}

function undo() {
    if (numMoves == 0) {
        // the whole game is taken back, go back to the game before it
        if (gameIndex > 0) {
            games[gameIndex] = currentGame();
            loadGame(gameIndex - 1);
            storeGames();
        }
        return;
    }
    // the moves that the current level makes by itself are undone together
    // with the move that caused them
    do {
        restoreSnapshot(undoLog.pop());
        numMoves--;
    } while (numMoves > 0 && markerOf(moves[numMoves]) <= automation);
    if (numMoves > 0) {
        // The state that is undone to may still allow moves that the current
        // level makes by itself, when the moves that follow were made on a
        // lower level.  Making them replaces the moves that were taken back:
        // they are a different continuation of the game, so there is nothing
        // left to redo.  Undoing the whole game is the exception, that always
        // shows the deal itself.
        automove();
    }
    storeGames();
    checkSolvable();
    updateBoard();
}

function redo() {
    if (numMoves >= moves.length) {
        // nothing left in this game, go on with the game after it
        if (gameIndex < games.length - 1) {
            games[gameIndex] = currentGame();
            loadGame(gameIndex + 1);
            storeGames();
        }
        return;
    }
    recording = false;
    do {
        var entry = moves[numMoves];
        if (!moveCard(sourceOf(entry), markerOf(entry))) {
            break;
        }
    } while (numMoves < moves.length && markerOf(moves[numMoves]) <= automation);
    recording = true;
    storeGames();
    checkSolvable();
    updateBoard();
}

function toggleChecking() {
    isChecking = !isChecking;
    checkSolvable();
}

// The setting is used by the next new game; the game on the board stays as it
// is, it may well be one that cannot be won.
function toggleEnsureSolvable() {
    ensureSolvable = !ensureSolvable;
    storeGames();
    updateOptionsBox();
}

function keypress(e) {
    if (e.which == 'r'.charCodeAt(0)) {
        redo();
    }
    if (e.which == 'u'.charCodeAt(0)) {
        undo();
    }
    if (e.which == 'c'.charCodeAt(0)) {
        toggleChecking();
    }
    if (e.which == 'n'.charCodeAt(0)) {
        // new game
        newGame();
    }
    if (e.which == 'f'.charCodeAt(0)) {
        toggleFullscreen();
    }
    if (e.which == 'o'.charCodeAt(0)) {
        toggleOptions();
    }
    if (e.which == 'e'.charCodeAt(0) && optionsOpen()) {
        // like the automation levels this is only visible in the option box
        toggleEnsureSolvable();
    }
    if (e.which == 'a'.charCodeAt(0) && optionsOpen()) {
        // cycle through the automation levels; only while the option box
        // shows them, the level changes nothing that can be seen otherwise
        setAutomation((automation + 1) % AUTO_LEVELS);
    }
    if (e.which == 32) {
        // space
        if (gameOver()) {
            newGame();
        }
    }
}

function isFullscreen() {
    var doc = window.document;
    return !!(doc.fullscreenElement || doc.mozFullScreenElement
              || doc.webkitFullscreenElement || doc.msFullscreenElement);
}

function toggleFullscreen() {
    var doc = window.document;
    var docEl = doc.documentElement;

    var requestFullScreen = docEl.requestFullscreen || docEl.mozRequestFullScreen || docEl.webkitRequestFullScreen || docEl.msRequestFullscreen;
    var cancelFullScreen = doc.exitFullscreen || doc.mozCancelFullScreen || doc.webkitExitFullscreen || doc.msExitFullscreen;

    if (!isFullscreen()) {
        requestFullScreen.call(docEl);
    } else {
        cancelFullScreen.call(doc);
    }
}

function highlightCard(evt) {
    var pt = svg.createSVGPoint()
    pt.x = evt.clientX;
    pt.y = evt.clientY;

    // The cursor point, translated into svg coordinates
    var cursorpt =  pt.matrixTransform(svg.getScreenCTM().inverse());

    var col = Math.floor((cursorpt.x-xoffset/2)/xgrid);
    if (col < 0 || col > 10) {
        return true;
    }
    var card = 0;
    if (cursorpt.y < 200) {
        if (col == 2 || col == 7) {
            return true;
        }
        if (col >= 3 && col < 7) {
            card = spots[col - 3];
        } else if (col < 2 && aces[col] < 13) {
            highlightedCard = aces[col] + 1 + col * 13;
            updateBoard();
        } else if (col > 7 && aces[col - 6] < 13) {
            highlightedCard = aces[col - 6] + 1 + (col - 6) * 13;
            updateBoard();
        }				
    } else {
        var yflute = computeFluteDist(col);
        var row = (cursorpt.y-yoffset);
        if (row > (stacks[col] - 1) * ygrid + flutes[col] * yflute + 190) {
            return true;
        }
        if (stacks[col] > 0) {
            if (row < (stacks[col] - 1) * ygrid) {
                row = Math.floor(row / ygrid);
                card = pos2card[row * 10 + col];
            } else {
                row -= (stacks[col] - 1) * ygrid;
                row = Math.floor(row / yflute);
                card = pos2card[(stacks[col] - 1) * 10 + col];
                if (row > flutes[col]) {
                    row = flutes[col];
                }
                card -= row;
            }
        }
    }
    if ((card % 13) != 0) {
        highlightedCard = card + 1;
        updateBoard();
    }
    return false;
}

function clearHighlight(evt) {
    if (highlightedCard > 0) {
        highlightedCard = 0;
        updateBoard();
    }
}

function isCurrentState(data) {
    for (var i = 0; i < 10; i++) {
        if (data[i] != stacks[i]) {
            return false;
        }
    }
    for (var i = 0; i < 4; i++) {
        if ((kings[i] > 0) != ((data[10] & (1 << i)) != 0)) {
            return false;
        }
    }
    return true;
}

function showCog() {
    document.getElementById("cogwheels").style.visibility = "visible";
    document.getElementById("smallcog").classList.add("small");
    document.getElementById("mediumcog").classList.add("medium");
}

function hideCog() {
    document.getElementById("cogwheels").style.visibility = "hidden";
    document.getElementById("smallcog").classList.remove("small");
    document.getElementById("mediumcog").classList.remove("medium");
}

function handleSolverMessage(msg) {
    if (!msg.data.finalResponse || msg.data.data.length != 12
        || msg.data.callbackId != solverRequest) {
        // the answer to a question that is already outdated
        return;
    }
    if (isSearching) {
        if (msg.data.data[11] != 0) {
            // this deal cannot be won, take the next one
            dealGame();
            return;
        }
        // a solvable game was found; only the check shows that it is one
        isSearching = false;
        if (!isChecking) {
            hideCog();
            return;
        }
    }
    if (!isChecking || !isCurrentState(msg.data.data)) {
        return
    }
    hideCog();
    if (msg.data.data[11] == 0) {
        document.getElementById("tick").style.visibility = "visible";
    } else if (msg.data.data[11] == 2) {
        document.getElementById("cross").style.visibility = "visible";
    }
}

function checkSolvable() {
    document.getElementById("cross").style.visibility = "hidden";
    document.getElementById("tick").style.visibility = "hidden";

    if ((isChecking || isSearching) && solver) {
        var data = [...stacks];
        var kingmask = 0;
        for (var suit = 0; suit < 4; suit++) {
            if (kings[suit] > 0) {
                kingmask |= (1 << suit);
            }
        }
        data.push(kingmask);
        console.log("solve: "+data);
        solver.postMessage({"funcName":"solve", "data": data,
                            "callbackId": ++solverRequest});
        showCog();
    } else {
        hideCog();
    }
}

function init() {
    svg = document.getElementById("board");
    svg.onclick = clickboard;
    svg.oncontextmenu = highlightCard;
    svg.onmouseup = clearHighlight;
    document.getElementById("undo").onclick = undo;
    document.getElementById("redo").onclick = redo;
    document.getElementById("newgame").onclick = newGame;
    document.getElementById("check").onclick = toggleChecking;
    // the option box stays open while its settings are changed; every click
    // outside of it closes it again, so it must not reach the board
    document.getElementById("options").onclick = (evt => {
        toggleOptions();
        evt.stopPropagation();
    });
    document.getElementById("optionsbox").onclick =
        (evt => evt.stopPropagation());
    document.getElementById("ensure").onclick = toggleEnsureSolvable;
    document.getElementById("fullscreen").onclick = toggleFullscreen;
    for (let level = 0; level < AUTO_LEVELS; level++) {
        document.getElementById("auto" + level).onclick =
            () => setAutomation(level);
    }
    document.onfullscreenchange = updateOptionsBox;
    document.onwebkitfullscreenchange = updateOptionsBox;
    window.onkeypress = keypress;

    if (window.Worker) {
        solver = new Worker('solver.js');
        solver.onmessage = handleSolverMessage;
        solver.onerror = (err => console.log(err));
    }

    // The level is stored with every move, so it is only missing for a game
    // that was stored before the automation levels existed; such a game was
    // played with full automation.  A new player starts with the flutes.
    automation = JSON.parse(window.localStorage.getItem("seahavenAutomation"));
    if (automation === null) {
        automation = window.localStorage.getItem("seahavenGames") === null
            && window.localStorage.getItem("seahavenMoves") === null
            ? AUTO_FLUTE : AUTO_FULL;
    }
    ensureSolvable =
        JSON.parse(window.localStorage.getItem("seahavenEnsureSolvable")) === true;

    games = JSON.parse(window.localStorage.getItem("seahavenGames"));
    gameIndex = JSON.parse(window.localStorage.getItem("seahavenGameIndex"));
    if (!games || games.length == 0) {
        // an older version stored a single game
        var shuffledCards = JSON.parse(window.localStorage.getItem("seahavenShuffle"));
        if (shuffledCards) {
            pos2card.set(shuffledCards);
        } else {
            shuffleCards();
        }
        games = [{
            "shuffle": Array.from(pos2card),
            "moves": JSON.parse(window.localStorage.getItem("seahavenMoves")) || [],
            "numMoves": JSON.parse(window.localStorage.getItem("seahavenNumMoves")) || 0
        }];
    }
    if (typeof gameIndex != "number" || gameIndex < 0 || gameIndex >= games.length) {
        gameIndex = games.length - 1;
    }
    loadGame(gameIndex);
    storeGames();
}

init();
