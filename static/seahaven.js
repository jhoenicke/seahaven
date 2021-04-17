const ytop = 10; 

const xoffset = 10;
const xgrid = 150;
const yoffset = 220;
const ygrid = 40;
const yflute = 25;

var shuffled_cards = Array(52);
var stacks = Array(10);
var spots = Array(4).fill(0);
var flutes = Array(10).fill(0);
var aces = Array(4);
var kings = Array(4);
var svg;

var highlightedCard = 0;
var undoLog = [];
var redoLog = [];

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
    var html = '<image transform="translate(' + x + ' ' +y +
	    ')" href="c' + card + '.svg" />';
    if (card == highlightedCard) {
	html += '<image transform="translate(' + x + ' ' +y +
	    ')" href="hl.svg" />';
    }
    return html;
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
	    var card = shuffled_cards[10 * d + col];
	    html += card2html(card, xoffset + col * xgrid, yoffset + d * ygrid);
	    if (d == stacks[col] - 1) {
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
    redoLog.push(snap.srccol);
}

function findFreeColumn() {
    for (var i = 0; i < 10; i++) {
	if (stacks[i] == 0) {
	    var foundKing = false;
	    for (var j = 0; j < 4; j++) {
		if (kings[j] >= 10 && kings[j] % 10 == i) {
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
	kings[destcol - 10] += 10 * srcflute;
    }

    automove();
    updateBoard();
}

function moveSpot(srcspot) {
    var card = spots[srcspot];
    if (card == 0 || (card % 13) != 0) {
	// we can only move a king
	return;
    }
    var freecol = findFreeColumn();
    if (freecol < 0) {
	return;
    }
    var suit = Math.floor((card - 1) / 13);
    destcol = 10 + suit;
    kings[suit] = freecol;

    moveFromTo(-srcspot-1, card, 1, destcol);
}

function moveColumn(srccol) {
    var extra = countEmptySpots();
    var srccard = 0, srcflute;
    if (stacks[srccol] > 0) {
	var d = stacks[srccol] - 1;
	srccard = shuffled_cards[10*d + srccol];
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
	return;
    }

    if (srcflute > extra + 1) {
	return;
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
	    kings[suit] = freecol;
	}
    } else if (srccard - 13* suit + Math.floor(kings[suit] / 10) == 13) {
	destcol = 10 + suit;
    } else {
	for (var col = 0; col < 10; col++) {
	    if (stacks[col] > 0) {
		var d = stacks[col] - 1;
		destcard = shuffled_cards[10*d + col] - flutes[col];
		if (srccard + 1 == destcard) {
		    destcol = col;
		    break;
		}
	    }
	}
    }
    if (destcol == -1 && srcflute > extra) {
	return;
    }

    moveFromTo(srccol, srccard, srcflute, destcol);
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
		    var precard = shuffled_cards[10*d + col];
		    var card = shuffled_cards[10*(d+1) + col];
		    if (card + 1 == precard && card % 13 != 0) {
			stacks[col]--;
			flutes[col]++;
		    } else {
			break;
		    }
		}
		var d = stacks[col] - 1;
		var card = shuffled_cards[10 * d + col] - flutes[col];
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

function start() {
    for (var i = 0; i < 52; i++) {
	shuffled_cards[i] = i+1;
    }
    shuffle(shuffled_cards);

    undoLog = [];
    redoLog = [];
    flutes.fill(0);
    stacks.fill(5);
    kings.fill(0);
    aces.fill(0);
    spots[1] = shuffled_cards[50];
    spots[2] = shuffled_cards[51];

    automove();
    updateBoard();
}

function clickboard(evt) {
    var pt = svg.createSVGPoint()
    pt.x = evt.clientX;
    pt.y = evt.clientY;

    // The cursor point, translated into svg coordinates
    var cursorpt =  pt.matrixTransform(svg.getScreenCTM().inverse());

    var col = Math.floor((cursorpt.x-xoffset/2)/xgrid);
    redoLog = [];
    if (cursorpt.y > 220 && col >= 0 && col < 10) {
	moveColumn(col);
    }
    if (cursorpt.y < 200 && col >= 3 && col < 7) {
	moveSpot(col - 3);
    }
}

function checkUndo(e) {
    if (e.which == 'r'.charCodeAt(0)) {
	// redo
	if (redoLog.length > 0) {
	    move = redoLog.pop();
	    if (move < 0) {
		moveSpot(-move - 1);
	    } else {
		moveColumn(move);
	    }
	}
    }
    if (e.which == 'u'.charCodeAt(0)) {
	// undo
	if (undoLog.length > 0) {
	    restoreSnapshot(undoLog.pop());
	    updateBoard();
	}
    }
    if (e.which == 32) {
	// space
	if (gameOver()) {
	    start();
	}
    }
    if (e.which == 'n'.charCodeAt(0)) {
	// new game
	start();
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
	var row = (cursorpt.y-yoffset);
	if (row > (stacks[col] - 1) * ygrid + flutes[col] * yflute + 190) {
	    return true;
	}
	if (stacks[col] > 0) {
	    if (row < (stacks[col] - 1) * ygrid) {
                row = Math.floor(row / ygrid);
		card = shuffled_cards[row * 10 + col];
	    } else {
		row -= (stacks[col] - 1) * ygrid;
                row = Math.floor(row / yflute);
		card = shuffled_cards[(stacks[col] - 1) * 10 + col];
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

function init() {
    svg = document.getElementById("board");
    svg.onclick = clickboard;
    svg.oncontextmenu = highlightCard;
    svg.onmouseup = clearHighlight;
    window.onkeypress = checkUndo;
    start();
}

init();
