#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <emscripten/emscripten.h>

#define HEART 0
#define DIAM  1
#define CLUB  2
#define SPADE 3

#define ACE    1
#define JAKE  11
#define QUEEN 12
#define KING  13

#define EXTRAPILE 10

#define CARD(s,v) (((s)<<4) + (v))
#define VALUE(c)  (c & 0xf)
#define SUIT(c)   (c >> 4)


#define LOADFACTOR   3L/5
#define KINGPILE     16
#define FREESLOT     0xffff
#define SLOT_VISITED (uint16_t*)1
#define MAX_MOVES   100
#define MAX_BRANCH  12

#define SUCCESS 0
#define ABORTED 1
#define NOMOVE  2 

#define BIG_HASH_SIZE 32717        /* This is a double prime */
#define MAX_HASHES    23
#undef CHECK

typedef uint8_t CardType;

static CardType pos2card[10][5];
static int8_t card2pile[64];
static int8_t card2depth[64];

static const uint32_t pileHashes[10] = {
    16, 96, 576, 3456, 20736, 124416, 746496, 4478976, 26873856, 161243136
};

static uint16_t unsolvable[MAX_HASHES][BIG_HASH_SIZE];

typedef struct {
    uint32_t   hash;          /* (pileDepth[i]+1)+pileHashes[i] + piled kings */
    int8_t     pileDepth[10]; /* number of cards above flute; -1 if empty */
    uint8_t    pileFlute[10]; /* number of cards in flute; 1 if empty */
    int8_t     aces[4];       /* Last card on aces; CARD(suit,0) if empty */
    int8_t     kings[4];      /* First unfree card counted from king */
    int8_t     freeSpace;     /* number of free places in extra */
    int8_t     freePiles;     /* number of free piles */
    int8_t     busyAces;      /* bitmask of suits whose aces must be rechecked */
} SolverPosType;

typedef struct {
    int8_t     from;
    int8_t     to;
} SolverMoveType;

void SolverInit(void)
{
    memset(unsolvable, 0xff, sizeof(unsolvable));
}

#define MAX_LOADSTRING 100

static void SolverOutOfMemory(void) {
    emscripten_worker_respond_provisionally("oom", 3);
}

static bool growHash(void);

static uint16_t *getSlot(uint32_t key) {
    int32_t  hash;
    uint16_t entry;
    uint16_t *hashTable;

 rehash:
    hash = key % BIG_HASH_SIZE;
    entry = (uint16_t) (key >> 14);
    hashTable = &unsolvable[entry % MAX_HASHES][0];

    if (hashTable[hash] == entry)
        return SLOT_VISITED;

    hashTable[hash] = entry;
    return &hashTable[hash];
}

static void freeSlot(uint32_t key) {
    int32_t  hash;
    uint16_t entry;
    uint16_t *hashTable;

    hash = key % BIG_HASH_SIZE;
    entry = (uint16_t) (key >> 14);
    hashTable = &unsolvable[entry % MAX_HASHES][0];

    if (hashTable[hash] == entry) {
        hashTable[hash] = FREESLOT;
    }
}

static void SolverRemovedFlute(int pile, SolverPosType *game)
{
    int card, prevCard, suit;
    int depth, flute;
    uint32_t hash, pilehash;
    depth = game->pileDepth[pile];
    pilehash = pileHashes[pile];
    hash = game->hash;
    
 repeat:
    flute = 1;
    
    if (depth == 0) {
        game->freePiles++;
        goto done;
    }
    
    card = pos2card[pile][depth-1];
    suit = SUIT(card);
    prevCard = card - 1;
    
    /* merge flutes */
    while (depth > 1 && pos2card[pile][depth-2] == card + 1) {
        hash -= pilehash;
        flute++;
        depth--; 
        card++;
    }
    
 check_ace:
    /*
     * check if flute can be moved to aces.
     */
    if (game->aces[suit] == prevCard) {
        game->aces[suit] = card;
        hash -= pilehash;
        depth--;
        game->busyAces |= 1 << suit;
        goto repeat;
    }
    
    /* check if card from extra can be appended to flute 
     */
    if (card2depth[prevCard] >= game->pileDepth[card2pile[prevCard]]) {
        game->freeSpace++;
        flute++;
        prevCard--;
        goto check_ace;
    }

    /* check if flute is a single king flute and move to kings */
    if (depth == 1 && VALUE(card) == KING) {
        hash = hash - pilehash + (1 << suit);
        depth = 0;
        flute = 1;
        game->kings[suit] = prevCard;
    }
  
 done:
    game->hash = hash;
    game->pileDepth[pile] = depth;
    game->pileFlute[pile] = flute;
}    

static void SolverRemoveFlute(int pile, SolverPosType *game)
{
    game->pileDepth[pile]--;
    game->hash -= pileHashes[pile];
    SolverRemovedFlute(pile, game);
}

static void SolverMoveAces(SolverPosType *game)
{
    while (game->busyAces) {
        int suit, card;
        int found;
        int suitBit;
        
        suit = 0;
        suitBit = 1;
        while (!(game->busyAces & suitBit)) {
            suit++;
            suitBit += suitBit;
        }
        
        card = game->aces[suit] + 1;
        found = 0;
        while (VALUE(card) <= KING) {
            int pile, cardDepth;
            pile = card2pile[card];
            cardDepth = card2depth[card] + 1 - game->pileDepth[pile];
            if (cardDepth > 0) {
                found++;
                /* The card is accessible from elsewhere */
                if (VALUE(card) == KING) {
                    game->kings[suit] = card;
                    game->aces[suit] = card;
                    if (game->hash & (1 << suit)) {
                        /* It is a king in a king suit */
                        game->hash -= suitBit;
                        game->freePiles++;
                    } else {
                        /* It is a king on space */
                        game->freeSpace += found;
                    }
                    break;
                }
                card++;
            } else if (cardDepth == 0) {
                /* We found the pile from which we can remove the flute, 
                 * just normalize it.
                 */
                game->aces[suit] = card;
                SolverRemoveFlute(pile, game);
                card = game->aces[suit] + 1;
                found = 0;
            } else {
                /* card is unaccessible, but the previous cards were
                   on extra */
                game->freeSpace += found;
                game->aces[suit] = card - 1;
                break;
            }
        }
        game->busyAces -= suitBit;
    }
}

static int SolverGenMoves(SolverPosType * game, 
                          SolverMoveType moves[MAX_BRANCH])
{
    int pile, suit;
    int depth, card, prevCard, fromPile, flute;
    int movedPiles = 0;
    int numMoves = 0;

    /* Get the possible moves that create new king piles */
    if (game->freePiles > 0
        && (game->hash & 15) != 15) {
        int spaceking = 0;
        for (suit = 0; suit < 4; suit++) {
            if (!(game->hash & (1 << suit))) {
                int cardDepth;
                card = CARD(suit,KING);
                fromPile = card2pile[card];
                cardDepth = card2depth[card] + 1 - game->pileDepth[fromPile];
                if (cardDepth > 0 && game->aces[suit] != card) {
                    if (cardDepth > 0) {
                        moves[numMoves].from = EXTRAPILE + suit;
                        moves[numMoves].to   = KINGPILE + suit;
                        spaceking = 1;
                        numMoves++;
                    } else if (game->pileFlute[fromPile]
                               <= game->freeSpace + 1) {
                        /* Note that these moves may be removed later */
                        moves[numMoves].from = fromPile;
                        moves[numMoves].to   = KINGPILE + suit;
                        numMoves++;
                    }
                }
            }
        }
        /* If there is a free pile and a king on space only allow these
         * kind of moves.
         */
        if (spaceking)
            return numMoves;
        /* Otherwise reset the moves.  We want the fromPile to king pile
         * moves to come later.
         */
        numMoves = 0;
    }
    
    /* Last check for king to space moves.
     * Do this last, since it may results in loops.
     * But moves are done backwards, so put unlikely moves first.
     */
    for (suit = 0; suit < 4; suit++) {
        if ((game->hash & (1 << suit))
            && game->freePiles == 0
            && KING - VALUE(game->kings[suit]) <= game->freeSpace) {
            
            /* We found a possible king2space move, but check if we
             * really need this space 
             */
            int i;
            for (i = 0; i < 4; i++) {
                card = CARD(i, KING);
                if (!(game->hash & (1 << i))
                    && card2depth[card] + 1 >= game->pileDepth[card2pile[card]]
                    && game->aces[i] != card) {
                    moves[numMoves].from = KINGPILE + suit;
                    moves[numMoves].to = EXTRAPILE;
                    numMoves++;
                    break;
                }
            }
        }
    }

    /* Now check for pile to pile moves */
    for (pile = 0; pile < 10; pile++) {
        depth = game->pileDepth[pile];
        if (depth == 0)
            continue;
        card = pos2card[pile][depth-1];
        prevCard = card - game->pileFlute[pile];
        fromPile = card2pile[prevCard];
        if (card2depth[prevCard] + 1 == game->pileDepth[fromPile]) {
            /* We found a possible pile2pile move */
            if (game->pileFlute[fromPile] <= game->freeSpace + 1) {
                movedPiles |= 1 << fromPile;
                moves[numMoves].from = fromPile;
                moves[numMoves].to   = pile;
                numMoves++;
            }
        }
    }
    
    /* Now check for pile to kings moves.
     */
    for (suit = 0; suit < 4; suit++) {
        prevCard = game->kings[suit];
        fromPile = card2pile[prevCard];
            
        if (card2depth[prevCard] + 1 == game->pileDepth[fromPile]) {
            /* We found a possible pile2king move */
            movedPiles |= 1 << fromPile;
            if (game->pileFlute[fromPile] <= game->freeSpace
                || (game->pileFlute[fromPile] <= game->freeSpace + 1
                    && (game->freePiles > 0
                        || (game->hash & (1 << suit))))) {
                moves[numMoves].from = fromPile;
                moves[numMoves].to   = KINGPILE + suit;
                numMoves++;
            }
        }
    }
    
    for (pile = 0; pile < 10; pile++) {
        if (!(movedPiles & (1 << pile))
            && game->pileDepth[pile] > 0
            && game->pileFlute[pile] <= game->freeSpace) {
            /* We found a pile2space move */
            moves[numMoves].from = pile;
            moves[numMoves].to = EXTRAPILE;
            numMoves++;
        }
    }
    
    return numMoves;
}

static void SolverMove(SolverPosType *game, SolverMoveType move)
{
    /* There are 5 possibile kinds of moves
     *
     *  space -> king
     *  pile  -> king
     *  pile  -> pile
     *  pile  -> space
     *  king  -> space
     */
    if (move.from < 10) {
        
        if (move.to < 10) {
            /* from pile to pile */
            game->pileFlute[move.to] += game->pileFlute[move.from];
        } else if (move.to == EXTRAPILE) {
            /* from pile to space */
            game->freeSpace -= game->pileFlute[move.from];
        } else {
            /* from pile to king */
            int suit = move.to - KINGPILE;
            if (!(game->hash & (1<<suit))) {
                if (game->freePiles > 0) {
                    game->freePiles--;
                    game->hash += 1 << suit;
                } else {
                    game->freeSpace -= game->pileFlute[move.from];
                }
            }
            game->kings[suit] -= game->pileFlute[move.from];
        }
        SolverRemoveFlute(move.from, game);
        if (game->busyAces)
            SolverMoveAces(game);

    } else if (move.from < KINGPILE) {
        /* from space to king */
        int suit = move.to - KINGPILE;
        game->freeSpace += KING - VALUE(game->kings[suit]);
        game->freePiles--;
        game->hash += 1 << suit;
        
    } else {
        /* from king to space */
        int suit = move.from - KINGPILE;
        game->freeSpace -= KING - VALUE(game->kings[suit]);
        game->freePiles++;
        game->hash -= 1 << suit;
    }
}

typedef struct {
    SolverPosType pos;
    int numMoves;
    SolverMoveType moves[MAX_BRANCH];
} GameStack;

GameStack stack[MAX_MOVES];

static int SolverIsSolvable(SolverPosType *game) {
    uint16_t *slot;
    GameStack *stackPtr = stack;


    /* No, I don't love goto, but sometimes they're quite nice :)
     *
     * This could be done recursively, of course, but the stack is
     * valuable.
     */

 checkSolvable:
    if (game->hash == 0)
        goto solved;
        
    if (stackPtr - stack >= MAX_MOVES)
        goto oom;
    
    slot = getSlot(game->hash);
    if (slot == SLOT_VISITED)
        goto notSolvable;

    if (!slot)
        goto abort;
    
    stackPtr->numMoves = SolverGenMoves(game, stackPtr->moves);
    stackPtr->pos      = *game;
    
 nextMove:
    if (stackPtr->numMoves-- > 0) {
        SolverMove(game, stackPtr->moves[stackPtr->numMoves]);
        stackPtr++;
        goto checkSolvable;
    }

 notSolvable:
    /* reduce depth and try next move */
    if (stackPtr-- > stack) {
        *game = stackPtr->pos;
        goto nextMove;
    }
    return NOMOVE;

 solved:
    /* The game is solvable */
    while (stackPtr-- > stack)
        freeSlot(stackPtr->pos.hash);
    return SUCCESS;

 oom:
    SolverOutOfMemory();

 abort:
    /* We have to abort, remove all cached positions from stack. */
    while (stackPtr-- > stack)
        freeSlot(stackPtr->pos.hash);
    return ABORTED; 
}

static void SolverConvertFromPilesKings(uint8_t* pilesking, SolverPosType *game)
{
    uint8_t kingmask = pilesking[10];
    int i;
    game->hash = kingmask;
    game->busyAces = 0;
    game->freeSpace = 4 - 52;
    game->freePiles = 0;
    for (i = 0; i < 10; i++) {
	int depth = pilesking[i];
	game->pileDepth[i] = depth;
        if (depth > 0) {
            game->hash      += pileHashes[i] * depth;
	    int card = pos2card[i][game->pileDepth[i]-1] - 1;
	    int flutelen = 1;
	    while (card2depth[card] >= pilesking[card2pile[card]]) {
		flutelen++;
		card--;
	    }
	    game->pileFlute[i] = flutelen;
	    game->freeSpace += depth + flutelen - 1;
        } else {
            game->pileFlute[i] = 1;
            game->freePiles++;
        }
    }
    for (i = 0; i < 4; i++) {
        int card = CARD(i, KING);
        int count = 0;

	int ace = CARD(i, ACE);
	while (ace <= card &&
	       card2depth[ace] >= game->pileDepth[card2pile[ace]]) {
	    ace++;
	}
	ace--;
	game->aces[i] = ace;
        game->freeSpace += VALUE(ace);
        if (ace < card) {
            while (card2depth[card] >= game->pileDepth[card2pile[card]]) {
                count++;
                card--;
            }
        }
	if (count > 0) {
	    if ((kingmask & (1 << i))) {
		game->freeSpace += count;
		game->freePiles--;
	    }
	}
        game->kings[i] = card;
    }
}

void initcard(uint8_t *cardshuffle, int size) {
    int i;
    SolverInit();
    for (i = 0; i < 52; i++) {
	int suit = (cardshuffle[i] - 1)/13;
	int card = CARD(suit, cardshuffle[i] - 13 * suit);
	card2pile[card] = i % 10;
	card2depth[card] = i / 10;
	if (i < 50) {
	    pos2card[i%10][i/10] = card;
	}
    }
}

void solve(uint8_t* stacks, int size) {
    SolverPosType game;
    char result[12];
    memcpy(result, stacks, 11);

    SolverConvertFromPilesKings(stacks, &game);
    if (game.hash == 0) {
        /* game is already solved */
	result[11] = SUCCESS;
    } else {
	result[11] = SolverIsSolvable(&game);
    }
    emscripten_worker_respond(result, 12);
}

