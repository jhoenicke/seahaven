#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#ifndef STANDALONE
#include <emscripten/emscripten.h>
#else

static void emscripten_worker_respond_provisionally(char *buffer, int len) {
    printf("ERR: ");
    for (int i = 0; i < len; i++) {
        printf("%d,", buffer[i]);
    }
    printf("\n");
}
static void emscripten_worker_respond(char *buffer, int len) {
    printf("RES: ");
    for (int i = 0; i < len; i++) {
        printf("%d,", buffer[i]);
    }
    printf("\n");
}
#endif

#define ACE    1
#define KING  13

#define CARD(s,v) (((s)<<4) + (v))
#define VALUE(c)  ((c) & 0xf)
#define SUIT(c)   ((c) >> 4)


#define KINGPILE     10
#define EXTRA        14
#define FREESLOT     0xff
#define MAX_MOVES   50

#define SUCCESS 0
#define ABORTED 1
#define NOMOVE  2 

#define BIG_HASH_SIZE (1024*1024)

typedef uint8_t CardType;

typedef struct {
    uint32_t   hash;          /* (pileDepth[i]+1)+pileHashes[i] */
    int8_t     pileDepth[10]; /* number of cards above flute; 0 if empty */
    uint8_t    pileFlute[10]; /* number of cards in flute; 1 if empty */
    int8_t     aces[4];       /* Last card on aces; CARD(suit,0) if empty */
    int8_t     kings[4];      /* First unfree card counted from king (CARD(suit, KING) if king isn't free) (even if there is no king pile) */
    int8_t     usedSpace;     /* number of cards in extra or on king piles */
    int8_t     freePiles;     /* number of free piles */
    int8_t     busyAces;      /* bitmask of suits whose aces must be rechecked */
} SolverPosType;

static CardType pos2card[10][5];
static uint8_t card2pile[64];
static uint8_t card2depth[64];
static uint16_t hashmap[BIG_HASH_SIZE];
static SolverPosType gameStack[MAX_MOVES];


static const uint32_t pileHashes[10] = {
    1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616, 10077696
};
static const uint8_t bits2grlex[16] = {
    0, 1, 2, 5, 3, 6, 7, 11, 
    4, 8, 9, 12, 10, 13, 14, 15
};
static const uint8_t grlex2bits[16] = {
    0, 1, 2, 4, 8,
    3, 5, 6, 9, 10, 12,
    7, 11, 13, 14, 15
};


void SolverInit(void)
{
    memset(hashmap, 0, sizeof(hashmap));
}

static uint32_t hit;
static uint32_t miss;

static uint8_t ctz(uint8_t bits) {
    return __builtin_ctz(bits);
}

typedef struct {
    uint8_t   shiftValue;
    uint8_t   numBits;
    uint8_t   offset;
} ClosureInfo;

static const ClosureInfo closureInfos[11] = {
    { 15,  5, 98 },
    { 11, 10, 0 },
    { 5, 10, 16 },
    { 1, 1, 80 },
    { 0, 1, 96 },
    { 0, 1, 96 },
    { 0, 1, 96 },
    { 0, 1, 96 },
    { 0, 1, 96 },
    { 0, 1, 96 },
    { 0, 1, 96 },
};

//0   4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
static const uint8_t componentTable[100] = {
    // table for level 2
    0x00, 0x07, 0x19, 0x1f, 0x2a, 0x2f, 0x3b, 0x3f,
    0x34, 0x37, 0x3d, 0x3f, 0x3e, 0x3f, 0x3f, 0x3f,

    // table for level 3
    0x0, 0x3, 0x5, 0x7, 0x6, 0x7, 0x7, 0x7,
    0x9, 0xb, 0xd, 0xf, 0,   0xf, 0xf, 0xf,
    0xa, 0xb, 0,   0xf, 0xe, 0xf, 0xf, 0xf,
    0xb, 0xb, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xc, 0,   0xd, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xd, 0xf, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xe, 0xf, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,

    // table for level 4
    0x0, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
    0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,

    // table for level 5
    0x0, 0x0,
    // table for level 1
    0x00, 0x0f
};

//0   4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
static const uint16_t subsetTable[100] = {
    //table for level 2
    0x0000, 0x8800, 0x9000, 0x9800, 0xa000, 0xa800, 0xb000, 0xb800,
    0xc000, 0xc800, 0xd000, 0xd800, 0xe000, 0xe800, 0xf000, 0xf800,
    //table for level 3
    0x0000, 0x9820, 0xa840, 0xb860, 0xc880, 0xd8a0, 0xe8c0, 0xf8e0,
    0xb100, 0xb920, 0xb940, 0xb960, 0xf980, 0xf9a0, 0xf9c0, 0xf9e0,
    0xd200, 0xda20, 0xfa40, 0xfa60, 0xda80, 0xdaa0, 0xfac0, 0xfae0,
    0xf300, 0xfb20, 0xfb40, 0xfb60, 0xfb80, 0xfba0, 0xfbc0, 0xfbe0,
    0xe400, 0xfc20, 0xec40, 0xfc60, 0xec80, 0xfca0, 0xecc0, 0xfce0,
    0xf500, 0xfd20, 0xfd40, 0xfd60, 0xfd80, 0xfda0, 0xfdc0, 0xfde0,
    0xf600, 0xfe20, 0xfe40, 0xfe60, 0xfe80, 0xfea0, 0xfec0, 0xfee0,
    0xf700, 0xff20, 0xff40, 0xff60, 0xff80, 0xffa0, 0xffc0, 0xffe0,
    // table for level 4
    0x0000, 0xb962, 0xdaa4, 0xffe6, 0xecc8, 0xffea, 0xffec, 0xffee,
    0xf710, 0xfff2, 0xfff4, 0xfff6, 0xfff8, 0xfffa, 0xfffc, 0xfffe,
    // table for level 5
    0x0000, 0xffff,
    //table for level 1
    0x0000, 0x8000
};

typedef struct {
    uint16_t possibleKings[6];
} KingInfo;

static uint8_t getSlot(uint32_t key) {
    uint32_t entry;
    uint32_t high = (key / BIG_HASH_SIZE) + 1;
    
    entry = ((high * 0x10001) ^ key) & (BIG_HASH_SIZE - 1);
    if (((hashmap[entry]^high) & 0x1ff) != 0) {
        return FREESLOT;
    } else {
        return (uint8_t) (hashmap[entry] >> 9);
    }
}

static void setSlot(uint32_t key, uint16_t value) {
    uint32_t entry;
    uint32_t high = (key / BIG_HASH_SIZE) + 1;
    
    entry = ((high * 0x10001) ^ key) & (BIG_HASH_SIZE - 1);
    hashmap[entry] = (value << 9) | (high & 0x1ff); 
}


static uint16_t computeComponentKingBits(SolverPosType *game) {
    int emptyPiles = game->freePiles;
    if (emptyPiles >= 1 && emptyPiles <= 3) {
        const ClosureInfo *info = &closureInfos[emptyPiles - 1];
        uint16_t result = 0;
        for (int i = 0; i < info->numBits; i++) {
            int usedSpace = game->usedSpace;
            uint8_t kingBitmap = grlex2bits[info->shiftValue + i];
            for (int suit = 0; suit < 4; suit++) {
                if ((kingBitmap & (1 << suit)) == 0) {
                    // king on pile
                    usedSpace -= KING - VALUE(game->kings[suit]);
                }
            }
            if (usedSpace <= 4) {
                result |= (1 << i);
            }
        }
        return componentTable[info->offset + result];
    } else {
        return 0;
    }
}

static void computeKingSpaces(int shiftValue, int neededBits, KingInfo *kingInfo, SolverPosType *game) {
    memset(kingInfo, 0, sizeof(KingInfo));

    for (int i = 0; i < neededBits; i++) {
        int usedSpace = game->usedSpace;
        uint8_t kingBitmap = grlex2bits[shiftValue + i];
        for (int suit = 0; suit < 4; suit++) {
            if ((kingBitmap & (1 << suit)) == 0) {
                // king on pile
                usedSpace -= KING - VALUE(game->kings[suit]);
            }
        }
        uint16_t bit = (1 << (shiftValue + i));
        while (usedSpace <= 4) {
            kingInfo->possibleKings[4 - usedSpace] |= bit;
            usedSpace++;
        }
    }
}

//0   4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
uint16_t kingOnPileMap[4] = {
    
    0x469d, 0x255b,  0x1337, 0x08ef
};

static uint8_t solverGetDestination(SolverPosType *game, int pile) {
    uint8_t card = pos2card[pile][game->pileDepth[pile] - 1];
    int suit = SUIT(card);
    if (card == game->kings[suit]) {
        return KINGPILE + suit;
    }
    int toPile;
    int posFromTop;
    do {
        card++;
        toPile = card2pile[card];
        posFromTop = game->pileDepth[toPile] - card2depth[card];
    } while (posFromTop <= 0);
    return posFromTop == 1 ? toPile : 14;
}

static void SolverRemoveFlute(int pile, SolverPosType *game)
{
    int card, prevCard, suit;
    int depth, flute;
    uint32_t hash, pilehash;
    assert(pile >= 0 && pile < 10);
    depth = game->pileDepth[pile];
    pilehash = pileHashes[pile];
    hash = game->hash;
    
    depth--;
    hash -= pilehash;
    flute = 1;

    if (depth == 0) {
        game->freePiles++;
    } else {
        card = pos2card[pile][depth-1];
        suit = SUIT(card);
        prevCard = card - 1;
        
        assert(card < 0x40 && VALUE(card) >= 1 && VALUE(card) <= KING);
        /* merge flutes */
        while (depth > 1 && pos2card[pile][depth-2] == card + 1) {
            depth--;
            hash -= pilehash;
            flute++;
            card++;
            assert(card < 0x40 && VALUE(card) >= 1 && VALUE(card) <= KING);
        }

        /* check if card from extra can be appended to flute 
         */
        while (game->aces[suit] < prevCard 
            && card2depth[prevCard] >= game->pileDepth[card2pile[prevCard]]) {
            flute++;
            prevCard--;
            game->usedSpace--;
        }

        /*
         * check if flute can be moved to aces.
         */
        if (game->aces[suit] == prevCard) {
            game->busyAces |= 1 << suit;
        }

        /* check if flute is a single king flute and move to kings */
        if (depth == 1 && VALUE(card) == KING) {
            assert(suit == SUIT(card));
            game->freePiles++;
            game->usedSpace += flute;
            game->kings[suit] -= flute;
            hash = hash - pilehash;
            depth = 0;
            flute = 1;
        }
    }

    game->hash = hash;
    game->pileDepth[pile] = depth;
    game->pileFlute[pile] = flute;
}    

static void SolverMoveAces(SolverPosType *game)
{
    int suit, card;
    int found;
    int suitBit;
    
    suit = ctz(game->busyAces);
    
    card = game->aces[suit] + 1;
    found = 0;
    while (VALUE(card) <= KING) {
        int pile, cardDepth;
        pile = card2pile[card];
        cardDepth = card2depth[card] + 1 - game->pileDepth[pile];
        if (cardDepth > 0) {
            found++;
            card++;
        } else if (cardDepth == 0) {
            /* We found the pile from which we can remove the flute, 
             * just normalize it.
             */
            game->aces[suit] = card;
            SolverRemoveFlute(pile, game);
            found = 0;
            card++;
        } else {
            break;
        }
    }
    /* card is unaccessible, but the previous cards were
        on extra */
    card--;
    game->usedSpace -= found;
    game->aces[suit] = card;
    if (VALUE(card) == KING) {
        game->kings[suit] = card;
    }
    game->busyAces -= (1 << suit);
}

static void SolverMove(SolverPosType *game, int pile, int toPile)
{
    int fluteLen = game->pileFlute[pile];
    if (toPile < KINGPILE) {
        /* from pile to pile */
        game->pileFlute[toPile] += fluteLen;
    } else {
        assert(toPile == EXTRA || toPile - 10 == SUIT(pos2card[pile][game->pileDepth[pile]-1]));
        /* to king or space */
        if (toPile < EXTRA) {
            game->kings[toPile - KINGPILE] -= fluteLen;
        }
        game->usedSpace += fluteLen;
    }
    SolverRemoveFlute(pile, game);
    while (game->busyAces)
        SolverMoveAces(game);
}

static uint16_t solverGetMovable(KingInfo *kingInfo, int fluteLen, int toPile) {
    if (fluteLen > 5) {
        return 0;
    }
    if (toPile < KINGPILE) {
        /* move is pile to pile */
        return kingInfo->possibleKings[fluteLen - 1];
    } else if (toPile < EXTRA) {
        /* move is to king */
        int kingOnPile = kingOnPileMap[toPile - KINGPILE];
        return kingInfo->possibleKings[fluteLen] | (kingInfo->possibleKings[fluteLen - 1] & kingOnPile);
    } else {
        return kingInfo->possibleKings[fluteLen];
    }
}

static uint16_t solverRecCheckSolvable(SolverPosType *game) {
    KingInfo kingInfo;
    const ClosureInfo *closureInfo = &closureInfos[game->freePiles];

    if (game->hash == 0) {
        return 1;
    }

    uint16_t cachedValue = getSlot(game->hash);
    if (cachedValue != FREESLOT) {
        hit++;
        // printf ("Hit: %08x %d%d%d%d%d%d%d%d%d%d %02x (%x)\n", 
        //     game->hash, 
        //     game->pileDepth[0],
        //     game->pileDepth[1],
        //     game->pileDepth[2],
        //     game->pileDepth[3],
        //     game->pileDepth[4],
        //     game->pileDepth[5],
        //     game->pileDepth[6],
        //     game->pileDepth[7],
        //     game->pileDepth[8],
        //     game->pileDepth[9],
        //     cachedValue, game->freePiles);
        return cachedValue;
    }
    miss++;
    // printf ("Mis: %08x %d%d%d%d%d%d%d%d%d%d ?? (%x)\n", 
    //     game->hash, 
    //     game->pileDepth[0],
    //     game->pileDepth[1],
    //     game->pileDepth[2],
    //     game->pileDepth[3],
    //     game->pileDepth[4],
    //     game->pileDepth[5],
    //     game->pileDepth[6],
    //     game->pileDepth[7],
    //     game->pileDepth[8],
    //     game->pileDepth[9],
    //     game->freePiles);

    computeKingSpaces(closureInfo->shiftValue, closureInfo->numBits, &kingInfo, game);
    // printf ("KingInfo: %04x,%04x,%04x,%04x,%04x\n", 
    //     kingInfo.possibleKings[0],
    //     kingInfo.possibleKings[1],
    //     kingInfo.possibleKings[2],
    //     kingInfo.possibleKings[3],
    //     kingInfo.possibleKings[4]);

    uint16_t allkings = kingInfo.possibleKings[0];
    uint16_t component = computeComponentKingBits(game) << closureInfo->shiftValue;
    uint16_t solvable = 0;
    assert(allkings != 0);
    assert((component & ~allkings) == 0);
    for (int pile = 0; pile < 10; pile++) {
        if (game->pileDepth[pile] == 0) {
            continue;
        }
        int fluteLen = game->pileFlute[pile];
        int toPile = solverGetDestination(game, pile);
        assert(toPile < KINGPILE || toPile == EXTRA || toPile - KINGPILE == SUIT(pos2card[pile][game->pileDepth[pile]-1]));
        uint16_t movable = solverGetMovable(&kingInfo, fluteLen, toPile) & allkings;
        if (movable & ~solvable) {
            game[1] = game[0];
            SolverMove(game + 1, pile, toPile);
            uint8_t recursiveSolvable = solverRecCheckSolvable(game + 1);
            // printf ("Try: %08x %d%d%d%d%d%d%d%d%d%d %04x (%x) %d %04x  -> %x\n", 
            //     game->hash, 
            //         game->pileDepth[0],
            //         game->pileDepth[1],
            //         game->pileDepth[2],
            //         game->pileDepth[3],
            //         game->pileDepth[4],
            //         game->pileDepth[5],
            //         game->pileDepth[6],
            //         game->pileDepth[7],
            //         game->pileDepth[8],
            //         game->pileDepth[9], movable & ~solvable,
            //         game->freePiles, pile, allkings, recursiveSolvable);
            movable &= subsetTable[closureInfos[game[1].freePiles].offset + recursiveSolvable];
            if (movable & component) {
                movable |= component;
            }
            solvable |= (movable & allkings);
            if (solvable == allkings)
                break;
        }
    }
    solvable >>= closureInfo->shiftValue;
    // printf ("Res: %08x %d%d%d%d%d%d%d%d%d%d %02x (%x)\n", 
    //     game->hash, 
    //     game->pileDepth[0],
    //     game->pileDepth[1],
    //     game->pileDepth[2],
    //     game->pileDepth[3],
    //     game->pileDepth[4],
    //     game->pileDepth[5],
    //     game->pileDepth[6],
    //     game->pileDepth[7],
    //     game->pileDepth[8],
    //     game->pileDepth[9],
    //     solvable, game->freePiles);
    setSlot(game->hash, solvable);
    assert (getSlot(game->hash) == solvable);
    return solvable;
}

static void SolverConvertFromPilesKings(uint8_t* pilesking, SolverPosType *game)
{
    int i;
    game->busyAces = 0;
    game->usedSpace = 52;
    game->freePiles = 0;
    game->hash = 0;
    for (i = 0; i < 10; i++) {
        int depth = pilesking[i];
        game->pileDepth[i] = depth;
        if (depth > 0) {
            game->hash += pileHashes[i] * depth;
            int card = pos2card[i][game->pileDepth[i]-1] - 1;
            int flutelen = 1;
            while (card2depth[card] >= pilesking[card2pile[card]]) {
                flutelen++;
                card--;
            }
            game->pileFlute[i] = flutelen;
            game->usedSpace -= depth + flutelen - 1;
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
        game->usedSpace -= VALUE(ace);
        if (ace < card) {
            while (card2depth[card] >= game->pileDepth[card2pile[card]]) {
                count++;
                card--;
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
    SolverPosType *game = &gameStack[0];
    char result[12];
    memcpy(result, stacks, 11);
    hit = 0;
    miss = 0;

    SolverConvertFromPilesKings(stacks, game);
    if (game->hash == 0) {
        /* game is already solved */
        result[11] = SUCCESS;
    } else {
        uint8_t kingbit = bits2grlex[stacks[10] ^ 0xf];
        uint8_t solvable = solverRecCheckSolvable(game);
        result[11] = (subsetTable[closureInfos[game[0].freePiles].offset + solvable] & (1 << kingbit)) != 0 ? SUCCESS : NOMOVE;
    }
    emscripten_worker_respond(result, 12);
    printf("Stats: %d hits %d misses\n", hit, miss);
}

#ifdef STANDALONE

int 
main() {
    uint8_t shuffle[52] = { 
        8,14,20,48,51,36,52,18,30,19,24,3,10,22,1,31,26,28,45,9,15,35,7,46,40,33,38,23,4,29,5,17,44,37,11,43,50,13,47,34,6,12,2,32,41,49,39,25,16,27,42,21
        //20,21,31,13,4,42,11,28,46,3,5,52,32,35,6,41,25,44,51,40,16,7,29,22,17,26,9,8,18,43,34,19,23,10,45,37,36,38,39,15,2,1,50,47,27,48,14,49,24,33,12,30
    };
    uint8_t stacks[11] = {
        1,5,1,4,0,0,0,5,5,4,14
        //0,0,0,2,0,0,0,0,1,4,15
        //1,3,5,2,2,3,1,4,4,3,0
        //0,3,5,0,0,3,1,4,2,3,5
        //4,4,5,5,4,5,4,5,5,5,0
        //5,5,5,5,5,5,5,5,5,5,0
    };

    initcard(shuffle, sizeof(shuffle));
    solve(stacks, sizeof(stacks));
    return 0;
}

#endif
