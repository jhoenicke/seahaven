# Seahaven Towers

Copyright 2021, Jochen Hoenicke.

## Try Online

https://jhoenicke.github.io/seahaven/

## Screenshot

<img src="https://github.com/jhoenicke/seahaven/blob/master/resources/screenshot.svg?raw=true" />

## Rules

The cards are initially dealt out into 10 tableau piles holding 5
cards each and the remaining two cards are dealt to the reserved
cells.  There are four reserved cells total, each can hold at most one
card.  The object of the game is to move all cards to the foundations
(at top left and right) from Ace to King by following suits.

On the tableau piles you can build down from King to Ace following
suit, the reserved cells can hold any card, but only one.  Empty
tableau piles may hold kings.  You can move the cards only one by one.
Only the lowest card from the tableau piles and the cards on reserved
cells are available.

The program will do some moves automatically: It will move all cards
to the foundations as soon as they get available.  It will move all
matching cards from the reserved cells back to the tableau piles.
When moving cards from the tableau piles it will move all cards of the
current suit as long as there is enough space in the reserved cells.
Also you just have to say which card to move, and the program will
automatically determine the destination.

If you think you're stuck you can check if the game is still solvable.
It will give you a tick or a cross as an answer.  If you're stuck you
can undo your moves to a position where the tick appears; the tick or
cross will update for every move.  If you're stuck on the initial
position that game had no solution.  Click the check button again to
hide the tick/cross.

## Compile and Install

First get the emscripten compiler.  Then run make in the solver
sub-directory. Finally copy the contents of the static sub-directory
to your web space.  Note that the solver uses WebWorker and does
not run on a local installation with file url.

## Credits

The cards use graphics from [Nicu's playing
cards](https://nicubunu.ro/cards/).  They also include glyphs from the
[Nimbus Sans](https://en.wikipedia.org/wiki/Nimbus_Sans) font.  The
final card layout is by me.  The animated gears are from [Garey
Simpson's CodePen](https://codepen.io/gareys/pen/meRgLG).  The tick and
checkbox icon are from the Open Clipart library: the
[cross](https://openclipart.org/detail/169757/check-and-cross-marks)
is by gcross, the
[tick](https://openclipart.org/detail/167549/green-tick-simple)
is by Kliponius.
