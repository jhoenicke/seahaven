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

var highlightedCard = 0;
var undoLog = [];
var moves = [];

var solver = null;
var isChecking = false;

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
    var html = '<use transform="translate(' + x + ' ' +y +
	    ')" xlink:href="#c' + card + '" />';
    if (card == highlightedCard) {
	html += '<use transform="translate(' + x + ' ' +y +
	    ')" xlink:href="#hl" />';
    }
    return html;
}

function storeMoves() {
    window.localStorage.setItem("seahavenMoves", JSON.stringify(moves));
    window.localStorage.setItem("seahavenNumMoves", JSON.stringify(numMoves));
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

function moveFromTo(srccol, srccard, srcflute, destcol) {
        
    undoLog.push(getSnapshot(srccol));

    if (srccol < 0) {
	spots[-srccol - 1] = 0;
    } else if (stacks[srccol] > 0) {
	stacks[srccol]--;
	flutes[srccol] = 0;
    } else {
	// move king to spots
	var suit = Math.floor((srccard - 1) / 13);
	kings[suit] = 0;
    }

    if (destcol == -1) {
	for (var i = 0; i < srcflute; i++) {
	    addSpot(srccard - i);
	}
    } else if (destcol < 10) {
	flutes[destcol] += srcflute;
    } else {
	// move to kings column
	suit = destcol - 10;
	if (kings[suit] == 0) {
	    kings[suit] = findFreeColumn();
	}
	kings[suit] += 10 * srcflute;
    }

    automove();
}

function moveSpot(srcspot) {
    var card = spots[srcspot];
    if (card == 0 || (card % 13) != 0) {
	// we can only move a king
	return false;
    }
    var freecol = findFreeColumn();
    if (freecol < 0) {
	return false;
    }
    var suit = Math.floor((card - 1) / 13);
    destcol = 10 + suit;

    moveFromTo(-srcspot-1, card, 1, destcol);
    return true;
}

function moveColumn(srccol) {
    var extra = countEmptySpots();
    var srccard = 0, srcflute;
    if (stacks[srccol] > 0) {
	var d = stacks[srccol] - 1;
	srccard = pos2card[10*d + srccol];
	srcflute = flutes[srccol] + 1;
    } else {
	for (var i = 0; i < 4; i++) {
	    if (kings[i] > 0 && (kings[i] % 10) == srccol) {
		srccard = i * 13 + 13;
		srcflute = Math.floor(kings[i] / 10);
		break;
	    }
	}
    }
    if (srccard == 0) {
	return false;
    }

    if (srcflute > extra + 1) {
	return false;
    }

    var suit = Math.floor((srccard - 1) / 13);
    var destcol = -1;
    if ((srccard % 13) == 0) {
	var freecol = -1
	if (stacks[srccol] != 0) {
	    freecol = findFreeColumn();
	}
	if (freecol >= 0) {
	    destcol = 10 + suit;
	}
    } else if (srccard - 13* suit + Math.floor(kings[suit] / 10) == 13) {
	destcol = 10 + suit;
    } else {
	for (var col = 0; col < 10; col++) {
	    if (stacks[col] > 0) {
		var d = stacks[col] - 1;
		destcard = pos2card[10*d + col] - flutes[col];
		if (srccard + 1 == destcard) {
		    destcol = col;
		    break;
		}
	    }
	}
    }
    if (destcol == -1 && srcflute > extra) {
	return false;
    }

    moveFromTo(srccol, srccard, srcflute, destcol);
    return true;
}

function move(m) {
    if (m < 0) {
  	 return moveSpot(-m - 1);
    } else {
         return moveColumn(m);
    }
}

function automove() {
    stable = false;
    while(!stable) {
	stable = true;
	for (var col = 0; col < 10; col++) {
	    for (var i = 0; i < 4; i++) {
		if (spots[i] > 0) {
		    var card = spots[i]
		    var suit = Math.floor((card - 1) / 13);
		    if (aces[suit] + 1 == card - 13*suit) {
			aces[suit]++;
			spots[i] = 0;
			stable = false;
		    }
		    if (card % 13 != 0 &&
			card - 13*suit + Math.floor(kings[suit] / 10) == 13) {
			kings[suit] += 10;
			spots[i] = 0;
			stable = false;
		    }
		}
	    }
	    if (stacks[col] > 0) {
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
		var d = stacks[col] - 1;
		var card = pos2card[10 * d + col] - flutes[col];
		var suit = Math.floor((card - 1) / 13);
		if (d == 0 && (card % 13) == 0) {
		    // move king to kings
		    kings[suit] = (1 + flutes[col]) * 10 + col;
		    stacks[col] = 0;
		    flutes[col] = 0;
		    stable = false;
		} else {
		    for (var i = 0; i < 4; i++) {
			if (spots[i] % 13 != 0 && spots[i] + 1 == card) {
			    spots[i] = 0;
			    flutes[col]++;
			    stable = false;
			}
		    }
		    if (aces[suit] + 1 == card - 13*suit) {
			aces[suit] += 1 + flutes[col];
			flutes[col] = 0;
			stacks[col]--;
			stable = false;
		    }
		}
	    }
	}
	for (var suit = 0; suit < 4; suit++) {
	    if (kings[suit] > 0) {
		var flutelen = Math.floor(kings[suit] / 10);
		if (flutelen + aces[suit] == 13) {
		    aces[suit] = 13;
		    kings[suit] = 0;
		}
	    }
	}
    }
}

function shuffleCards() {
    for (var i = 0; i < 52; i++) {
	pos2card[i] = i+1;
    }
    shuffle(pos2card);
    window.localStorage.setItem("seahavenShuffle", JSON.stringify(Array.from(pos2card)));
}

function newGame() {
    shuffleCards();
    moves = [];
    numMoves = 0;
    storeMoves();
    reset();
}

function reset() {
    if (solver) {
	solver.postMessage({funcName:"initcard", data: pos2card})
    }
    undoLog = [];
    flutes.fill(0);
    stacks.fill(5);
    kings.fill(0);
    aces.fill(0);
    spots.fill(0);
    spots[1] = pos2card[50];
    spots[2] = pos2card[51];

    automove();
    for (var i = 0; i < numMoves; i++) {
        move(moves[i]);
    }
    checkSolvable();
    updateBoard();
}

function makeMove(m) {
    if (move(m)) {
        while (moves.length > numMoves) {
            moves.pop();
        }
        moves.push(m);
        numMoves++;
        storeMoves();
	checkSolvable();
        updateBoard();
    }
}

function clickboard(evt) {
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
    if (undoLog.length > 0) {
	restoreSnapshot(undoLog.pop());
        numMoves--;
        storeMoves();
	checkSolvable();
	updateBoard();
    }
}

function redo() {
    if (numMoves < moves.length) {
        move(moves[numMoves++]);
        storeMoves();
	checkSolvable();
        updateBoard();
    }
}

function toggleChecking() {
    isChecking = !isChecking;
    checkSolvable();
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
    if (e.which == 32) {
	// space
	if (gameOver()) {
	    newGame();
	}
    }
}

function toggleFullscreen() {
    var doc = window.document;
    var docEl = doc.documentElement;

    var requestFullScreen = docEl.requestFullscreen || docEl.mozRequestFullScreen || docEl.webkitRequestFullScreen || docEl.msRequestFullscreen;
    var cancelFullScreen = doc.exitFullscreen || doc.mozCancelFullScreen || doc.webkitExitFullscreen || doc.msExitFullscreen;

    if(!doc.fullscreenElement && !doc.mozFullScreenElement && !doc.webkitFullscreenElement && !doc.msFullscreenElement) {
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
    if (msg.data.finalResponse && msg.data.data.length == 12) {
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
}

function checkSolvable() {
    document.getElementById("cross").style.visibility = "hidden";
    document.getElementById("tick").style.visibility = "hidden";

    if (isChecking) {
	var data = [...stacks];
	var kingmask = 0;
	for (var suit = 0; suit < 4; suit++) {
	    if (kings[suit] > 0) {
		kingmask |= (1 << suit);
	    }
	}
	data.push(kingmask);
	solver.postMessage({"funcName":"solve", "data": data});
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
    document.getElementById("fullscreen").onclick = toggleFullscreen;
    document.getElementById("check").onclick = toggleChecking;
    window.onkeypress = keypress;

    if (window.Worker) {
	solver = new Worker('solver.js');
	solver.onmessage = handleSolverMessage;
	solver.onerror = (err => console.log(err));
    }

    shuffledCards = JSON.parse(window.localStorage.getItem("seahavenShuffle"));
    if (shuffledCards) {
	pos2card.set(shuffledCards)
    } else {
        shuffleCards();
    }
    moves = JSON.parse(window.localStorage.getItem("seahavenMoves"));
    numMoves = JSON.parse(window.localStorage.getItem("seahavenNumMoves"));
    if (!moves) {
        moves = [];
        numMoves = 0;
	storeMoves();
    }   
    reset();
}

init();
