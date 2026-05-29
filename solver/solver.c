/*
 * Seahaven Towers solvability checker.
 *
 * Determines whether the current game state is solvable, and for which king
 * configurations.  The solver abstracts card positions into pile depths and
 * "flutes" (consecutive same-suit sequences at the accessible top of a pile
 * that must be moved together).  Because pile depths alone fully determine
 * the game state given a fixed initial card layout, results are memoised by a
 * hash of the pile depths.
 *
 * King configurations: each of the 4 suits may have its king sequence either
 * in a dedicated empty pile or tracked in usedSpace (extra cells).  The 16
 * possible combinations are indexed in grlex order.  In the grlex bitmask,
 * bit k SET means suit k's king is in extra slots (usedSpace, not occupying an
 * empty pile); bit k UNSET means suit k's king IS in a dedicated empty pile.
 * Grlex index 0 = all kings in dedicated empty piles (lowest, most piled);
 * grlex index 15 = all kings in extra slots, no dedicated piles (highest).
 * The return value of solverRecCheckSolvable is this grlex bitmask: bit i set
 * means the game is solvable when the kings are arranged per grlex2bits[i].
 * The hashtable stores only the bits relevant to "all free piles used for kings"
 * (i.e., exactly freePiles suits have dedicated empty piles).
 *
 * Compiled with -DSTANDALONE for testing; otherwise compiled as an Emscripten
 * web worker.
 */
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

/* Cards are encoded as (suit << 4) | value, values 1..13, suits 0..3. */
#define CARD(s,v) (((s)<<4) + (v))
#define VALUE(c)  ((c) & 0xf)
#define SUIT(c)   ((c) >> 4)


#define KINGPILE     10   /* move destination: suit's king pile (10..13 = suit 0..3) */
#define EXTRA        14   /* move destination: extra cells (temporary parking)        */
#define FREESLOT     0xff /* hashmap sentinel for an empty slot                       */
#define MAX_MOVES   50    /* maximum DFS depth (one per pile card)                    */

#define SUCCESS 0
#define ABORTED 1
#define NOMOVE  2

#define BIG_HASH_SIZE (1024*1024)

typedef uint8_t CardType;

/*
 * Abstract game state used by the solver.
 *
 * Each pile is split into two conceptual regions (bottom to top in pos2card):
 *   - above-flute section: cards at pos2card[pile][0 .. pileDepth-2], buried
 *     under the flute and inaccessible until the flute is moved.
 *   - flute: cards starting with card at pos2card[pile][pileDepth-1],
 *     a consecutive same-suit descending sequence at the accessible top.
 *     The boundary card (pos2card[pile][pileDepth-1]) has the highest value in
 *     the flute; the most accessible card has the lowest value.
 *
 * pileDepth == 0: pile is empty.
 * pileDepth == 1: pile contains only the flute (no above-flute cards).
 *
 * The flute is a unit of movement: moving a flute of length L to another pile
 * requires L-1 free extra slots (to park the interior cards temporarily) but
 * does not change usedSpace.  Moving a flute to extra uses L extra slots and
 * increases usedSpace by L.  It's never useful to move only a part of a flute,
 * because that would just fill up extra space, without freeing a new card.
 *
 * usedSpace counts cards currently occupying extra slots or sitting in king
 * piles.  Free extra slots = 4 - usedSpace - space used by piled kings. 
 * Moves are legal only when there is sufficient free extra space.
 *
 * The king configuration (which kings are in free piles and which are in
 * extra space) is not part of the abstract game state.  Instead we compute
 * for each game a bitmask of all solvable king configuration.  This keeps
 * the part of moving the kings between freed piles inside a single
 * game state node, avoiding cycles in the game state graph.
 *
 * The hash is sum(pileDepth[i] * pileHashes[i]).  Together with the fixed
 * initial card layout (pos2card / card2pile / card2depth), the pile depths
 * fully determine the game state (up to pile order/normalization), enabling
 * memoisation.
 */
typedef struct {
    uint32_t   hash;          /* weighted sum of pile depths, used as memoise key   */
    int8_t     pileDepth[10]; /* above-flute card count + 1; 0 if empty             */
    uint8_t    pileFlute[10]; /* flute length (>= 1 when pileDepth > 0)             */
    int8_t     aces[4];       /* highest card on foundation per suit; CARD(suit,0) if none */
    int8_t     kings[4];      /* first un-freed card counting down from king; equals
                               * CARD(suit,KING) when the king is not yet in a king 
                               * pile or extra slot */
    int8_t     usedSpace;     /* cards in extra slots + cards in king piles          */
    int8_t     freePiles;     /* number of empty piles                               */
    int8_t     busyAces;      /* bitmask: suits whose aces need re-evaluation        */
} SolverPosType;

/*
 * pos2card[pile][i]: the card at position i in pile (i=0 = physically deepest,
 * higher i = more accessible / lower value).  Only positions 0..4 are used
 * (at most 5 cards per pile in the initial deal).
 *
 * card2pile[card]: the pile the card was originally dealt into.
 * card2depth[card]: the position index of the card in its original pile.
 *
 * A card has been removed from its pile (moved to extra, foundation, or king
 * pile) when card2depth[card] >= pileDepth[card2pile[card]].
 */
static CardType pos2card[10][5];
static uint8_t card2pile[64];
static uint8_t card2depth[64];
static uint16_t hashmap[BIG_HASH_SIZE];
/* DFS stack: game[0] is the current frame, game[1] the child frame, etc. */
static SolverPosType gameStack[MAX_MOVES];


/* pileHashes[i] = 6^i, used to compute a position hash as a polynomial in the
 * pile depths.  Powers of 6 guarantee uniqueness of hash as pileDepth is always
 * between 0 and 5.  The hash fits in uint32_t.
 */
static const uint32_t pileHashes[10] = {
    1, 6, 36, 216, 1296, 7776, 46656, 279936, 1679616, 10077696
};

/*
 * Grlex (graded lexicographic) ordering of the 16 subsets of {suit0..suit3}.
 * Subsets are ranked first by the number of suits in extra slots (cardinality
 * of SET bits), then lexicographically within each rank.
 *
 * bits2grlex[bitmask] -> grlex index
 *   (bitmask: bit k SET = suit k's king is in extra slots / NOT in dedicated pile)
 * grlex2bits[index]   -> bitmask
 *
 * Grlex index layout (sets show which suits are in extra slots, others are piled):
 *   0        -> {} (all 4 kings in dedicated empty piles)
 *   1..4     -> {0},{1},{2},{3}                  (1 king in extra)
 *   5..10    -> {0,1},{0,2},{1,2},{0,3},{1,3},{2,3} (2 kings in extra)
 *   11..14   -> {0,1,2},{0,1,3},{0,2,3},{1,2,3}  (3 kings in extra)
 *   15       -> {0,1,2,3}                         (all kings in extra, no dedicated piles)
 */
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

/*
 * ClosureInfo describes the king-configuration encoding for a given freePiles
 * count.  Assuming all freePiles empty piles are reserved for king piles, the
 * relevant configurations are those with exactly freePiles suits in dedicated
 * piles (UNSET bits).  These form a contiguous range in the grlex ordering
 * (since configs with the same number of dedicated piles are adjacent).
 *
 * shiftValue: global grlex index of local bit 0 (smallest relevant config).
 * numBits:    number of relevant king configurations.
 * offset:     base index into componentTable / subsetTable for this freePiles.
 *
 * The solvable return value of solverRecCheckSolvable uses local bit numbering:
 * local bit i corresponds to global grlex index (shiftValue + i).
 *
 * Entries 0..10 cover freePiles = 0..10; entries 4..10 share the same values
 * since 4+ free piles allow all king configurations.
 */
typedef struct {
    uint8_t   shiftValue;
    uint8_t   numBits;
    uint8_t   offset;
} ClosureInfo;

static const ClosureInfo closureInfos[11] = {
    { 15,  1, 98 },   /* freePiles = 0 */
    { 11,  4, 0  },   /* freePiles = 1 */
    {  5,  6, 16 },   /* freePiles = 2 */
    {  1,  4, 80 },   /* freePiles = 3 */
    {  0,  1, 96 },   /* freePiles = 4 */
    {  0,  1, 96 },   /* freePiles = 5 */
    {  0,  1, 96 },   /* freePiles = 6 */
    {  0,  1, 96 },   /* freePiles = 7 */
    {  0,  1, 96 },   /* freePiles = 8 */
    {  0,  1, 96 },   /* freePiles = 9 */
    {  0,  1, 96 },   /* freePiles = 10 */
};

/*
 * componentTable[king configs with one truely empty pile] -> component bitmask.
 *
 * Among the admissible king configurations (those where freed-king cards fit in
 * extra space), there is at most one non-singleton strongly-connected component:
 * configurations where there is enough slack to temporarily displace a king
 * stack, replace it with another, and restore the first.  All other admissible
 * configurations are singletons (cannot reach any other configuration).
 *
 * The component bitmask has a bit set for every configuration that belongs to
 * this big component.  If a game position is solvable for one configuration in
 * a component, all configurations in that component are also solvable (by
 * reshuffling king pile assignments).
 *
 * Indexed by the bitmask for the admissible king configurations with one empty
 * pile, i.e., the bitmask containing the configuration with freePiles - 1
 * unset bits (dedicated piles) where there the freed-king cards fit in extra
 * space.
 *
 * The index is closureInfos[freePiles-1].offset + setOfConfigurations
 * for freePiles in {1,2,3}; unused outside that range.
 *
 * Column labels (grlex order):  0  4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
 */
static const uint8_t componentTable[100] = {
    // table for level 2 (freePiles = 2, 16 input combinations)
    0x00, 0x07, 0x19, 0x1f, 0x2a, 0x2f, 0x3b, 0x3f,
    0x34, 0x37, 0x3d, 0x3f, 0x3e, 0x3f, 0x3f, 0x3f,

    // table for level 3 (freePiles = 3, 64 input combinations)
    0x0, 0x3, 0x5, 0x7, 0x6, 0x7, 0x7, 0x7,
    0x9, 0xb, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xa, 0xb, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xb, 0xb, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xc, 0xf, 0xd, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xd, 0xf, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xe, 0xf, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,

    // table for level 4 (freePiles = 4, 16 input combinations); unused
    0x0, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
    0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,

    // table for level 5 (freePiles = 5+, 2 input combinations); unused
    0x0, 0x0,
    // table for level 1 (freePiles = 1, 2 input combinations)
    0x00, 0x0f
};

/*
 * subsetTable[childOffset + childSolvable] -> 16-bit parent bitmask.
 *
 * After making a move (transitioning from parent to child state), the child's
 * solvable king-config bitmask is translated back to the parent's space.
 * A parent configuration p is marked solvable if there exists a solvable child
 * configuration c such that the set of piled kings in p (suits with UNSET bits
 * in grlex2bits[p]) is a subset of the piled kings in c.  In other words: if
 * the child is solvable when c's empty piles are dedicated to kings, the parent
 * is also solvable for any sub-configuration p ⊆ c that uses fewer dedicated
 * piles.
 *
 * childOffset = closureInfos[child.freePiles].offset.
 * The result is shifted right by closureInfos[parent.freePiles].shiftValue to
 * align with the parent's local bit numbering.
 *
 * Column labels:  0  4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
 */
static const uint16_t subsetTable[100] = {
    //table for level 2 (child freePiles = 1)
    0x0000, 0x8800, 0x9000, 0x9800, 0xa000, 0xa800, 0xb000, 0xb800,
    0xc000, 0xc800, 0xd000, 0xd800, 0xe000, 0xe800, 0xf000, 0xf800,
    //table for level 3 (child freePiles = 2)
    0x0000, 0x9820, 0xa840, 0xb860, 0xc880, 0xd8a0, 0xe8c0, 0xf8e0,
    0xb100, 0xb920, 0xb940, 0xb960, 0xf980, 0xf9a0, 0xf9c0, 0xf9e0,
    0xd200, 0xda20, 0xfa40, 0xfa60, 0xda80, 0xdaa0, 0xfac0, 0xfae0,
    0xf300, 0xfb20, 0xfb40, 0xfb60, 0xfb80, 0xfba0, 0xfbc0, 0xfbe0,
    0xe400, 0xfc20, 0xec40, 0xfc60, 0xec80, 0xfca0, 0xecc0, 0xfce0,
    0xf500, 0xfd20, 0xfd40, 0xfd60, 0xfd80, 0xfda0, 0xfdc0, 0xfde0,
    0xf600, 0xfe20, 0xfe40, 0xfe60, 0xfe80, 0xfea0, 0xfec0, 0xfee0,
    0xf700, 0xff20, 0xff40, 0xff60, 0xff80, 0xffa0, 0xffc0, 0xffe0,
    // table for level 4 (child freePiles = 3)
    0x0000, 0xb962, 0xdaa4, 0xfbe6, 0xecc8, 0xfdea, 0xfeec, 0xffee,
    0xf710, 0xff72, 0xffb4, 0xfff6, 0xffd8, 0xfffa, 0xfffc, 0xfffe,
    // table for level 5 (child freePiles = 4+)
    0x0000, 0xffff,
    //table for level 1 (child freePiles = 0)
    0x0000, 0x8000
};

typedef struct {
    uint8_t possibleKings[6];
} KingInfo;

/*
 * One-slot open-addressing hash map.  Each entry stores a 7-bit value and a
 * 9-bit tag derived from the key, packed into a uint16_t.
 *
 * The tag disambiguates collisions: if the stored tag doesn't match the query,
 * the slot is treated as empty (FREESLOT).  This gives a single-probe lookup
 * with a very low false-hit rate; eviction silently replaces the old entry.
 */
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


/*
 * Computes the component bitmask for the current position.
 *
 * Among all admissible king configurations (those where freed king cards fit in
 * the available extra slots), some form a single reachable component: you can
 * cycle between them by temporarily moving the shortest king stack to extra,
 * freeing a slot, then moving the longest king stack into that slot.  This
 * works only when usedSpace is small enough to absorb one additional king stack.
 *
 * For 1..3 empty piles, first evaluates the configurations where one pile is
 * kept truely free and the other empty piles are dedicated to a king.  It creates
 * the bitmask, where the bit is one if the configuration is feasible, i.e., the
 * four extra cells are enough to hold the unpiled kings.
 *
 * All these configurations are reachable from each other: by iteratively moving
 * the largest king flute that should be dedicated to the empty pile and then freeing
 * the pile with the shortest king flute that should be on extra space, one can
 * reach any feasible configuration where one pile is empty.  From these one can
 * reach all configurations with one more dedicated king on the empty pile.  This
 * means that all the configurations that are a superset of a feasble configuation
 * with one fewer pile are forming a big component of admissible king configuations.
 * All other feasible configuarations with all piles dedicated are their own singleton
 * component.
 *
 * This function computes the big component of admissible king configurations.
 * Returns 0 if emptyPiles is 0 or >= 4 (no reshuffling needed or possible).
 */
static uint16_t computeComponentKingBits(SolverPosType *game) {
    int emptyPiles = game->freePiles;
    if (emptyPiles >= 1 && emptyPiles <= 3) {
        /* closureInfos[emptyPiles-1] covers configs with (emptyPiles-1) kings,
         * i.e., what happens when one king pile is temporarily moved to extra. */
        const ClosureInfo *info = &closureInfos[emptyPiles - 1];
        uint16_t result = 0;
        for (int i = 0; i < info->numBits; i++) {
            int usedSpace = game->usedSpace;
            uint8_t kingBitmap = grlex2bits[info->shiftValue + i];
            for (int suit = 0; suit < 4; suit++) {
                if ((kingBitmap & (1 << suit)) == 0) {
                    /* This suit's king is in a king pile; subtract its freed cards
                     * to find the effective extra-slot usage. */
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

/*
 * Populates kingInfo->possibleKings[k] with a bitmask of local king-config
 * indices that have at least k free extra slots.
 *
 * For each of the numBits configurations starting at grlex index shiftValue,
 * computes effective usedSpace (adjusting for which suits have king piles) and
 * records the config bit in possibleKings[0..4-usedSpace].
 *
 * possibleKings[k] is used by solverGetMovable to check whether a move that
 * temporarily needs k free extra slots is possible under each king config.
 */
static void computeKingSpaces(int shiftValue, int neededBits, KingInfo *kingInfo, SolverPosType *game) {
    memset(kingInfo, 0, sizeof(KingInfo));

    for (int i = 0; i < neededBits; i++) {
        int usedSpace = game->usedSpace;
        uint8_t kingBitmap = grlex2bits[shiftValue + i];
        for (int suit = 0; suit < 4; suit++) {
            if ((kingBitmap & (1 << suit)) == 0) {
                /* Suit's king is in a king pile; its freed cards are not in extra,
                 * so subtract them from the effective extra-slot usage. */
                usedSpace -= KING - VALUE(game->kings[suit]);
            }
        }
        uint8_t bit = (1 << i);
        while (usedSpace <= 4) {
            kingInfo->possibleKings[4 - usedSpace] |= bit;
            usedSpace++;
        }
    }
}

/*
 * For each suit s, kingOnPileMap[s] is a 16-bit mask (in grlex order) where
 * bit i is set iff suit s's king IS in a dedicated empty pile in configuration
 * grlex2bits[i] (i.e., bit s is UNSET in grlex2bits[i]).  Used to determine
 * whether a flute can land on suit s's king pile with one fewer extra slot
 * (the dedicated pile absorbs the flute boundary card directly).
 */
//0   4 3 2 1   34 24 23 14 13 12   234 134 124 123  1234
uint16_t kingOnPileMap[4] = {
    0x469d, 0x255b, 0x1337, 0x08ef
};

/*
 * Returns the destination for the flute at the top of pile.
 *
 * The flute's boundary card (pos2card[pile][pileDepth-1], highest value in
 * the flute) determines where it should go:
 *   - If the boundary card is the suit's current king frontier: KINGPILE+suit.
 *   - Otherwise: scan upward through the suit sequence to find the next card
 *     that is still in a pile at the top position (posFromTop == 1).  That
 *     pile is the destination.  If the target card is buried (posFromTop > 1),
 *     return EXTRA (must park in extra until it's unblocked).
 */
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

/*
 * After moving the current flute off pile, recomputes the pile's new flute.
 *
 * Decrements pileDepth by 1 (removing the old flute boundary card).  If the
 * newly exposed above-flute card continues a consecutive same-suit sequence
 * with the card below it, those cards are merged into the new flute
 * (pileDepth decrements further, pileFlute grows).
 *
 * Also checks if predecessor cards that were freed (in extra) can be appended
 * to the new flute, and whether the new flute can move to aces (sets busyAces).
 *
 * Special case: if the new single-card flute is a king, the pile becomes empty
 * (freePiles++) and the king moves to the king-pile tracking in kings[suit].
 */
static void SolverRemoveFlute(int pile, SolverPosType *game)
{
    int card, prevCard, suit;
    int depth, flute;
    uint32_t hash, pilehash;
    assert(pile >= 0 && pile < 10);
    depth = game->pileDepth[pile];
    pilehash = pileHashes[pile];
    hash = game->hash;

    /* Remove the old flute boundary: the pile shrinks by one depth level. */
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
        /* Merge consecutive same-suit cards below the new top into the flute. */
        while (depth > 1 && pos2card[pile][depth-2] == card + 1) {
            depth--;
            hash -= pilehash;
            flute++;
            card++;
            assert(card < 0x40 && VALUE(card) >= 1 && VALUE(card) <= KING);
        }

        /* Extend the flute with predecessor cards that have already been freed
         * from their original piles (they are in extra space).  Each such card
         * reduces usedSpace because it is now accounted for by this flute. */
        while (game->aces[suit] < prevCard
            && card2depth[prevCard] >= game->pileDepth[card2pile[prevCard]]) {
            flute++;
            prevCard--;
            game->usedSpace--;
        }

        /* If the predecessor of the flute is already on the foundation,
         * this flute can move to there; mark it for re-evaluation. */
        if (game->aces[suit] == prevCard) {
            game->busyAces |= 1 << suit;
        }

        /* A lone-king flute: the king has no cards above it, so the pile can be
         * vacated.  The king stack moves to king-pile tracking (usedSpace). */
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

/*
 * Moves as many cards of the given suit as possible from piles to the
 * foundation (aces pile), starting from game->aces[suit]+1.
 *
 * Walks up the suit's sequence from the current foundation top:
 *   - cardDepth > 0: card has already been freed from its pile (in extra);
 *     count it in `found` (these will be subtracted from usedSpace).
 *   - cardDepth == 0: card is at the top of its pile; advance the foundation
 *     and call SolverRemoveFlute to expose the next card.
 *   - cardDepth < 0: card is still buried; stop.
 *
 * At the end, subtracts `found` from usedSpace (freed cards that moved from
 * extra to foundation), and updates aces[suit] and kings[suit] accordingly.
 */
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
            /* Card is at top of its pile; advance foundation and recompute flute. */
            game->aces[suit] = card;
            SolverRemoveFlute(pile, game);
            found = 0;
            card++;
        } else {
            break;
        }
    }
    /* Cards counted in `found` were freed (in extra); moving to foundation
     * releases those extra slots. */
    card--;
    game->usedSpace -= found;
    game->aces[suit] = card;
    /* if we moved all cards including the king, mark the king suit as empty. */
    if (VALUE(card) == KING) {
        game->kings[suit] = card;
    }
    game->busyAces -= (1 << suit);
}

/*
 * Applies one solver move: move the flute from `pile` to `toPile`.
 *
 * toPile < KINGPILE:  pile-to-pile move.  The destination pile's flute grows
 *                     by the moved flute length (they merge at the boundary).
 * toPile >= KINGPILE && toPile < EXTRA:  move to king pile.  Increases
 *                     usedSpace and updates kings[suit].
 * toPile == EXTRA:    move to extra slots.  Increases usedSpace by the full
 *                     flute length.
 *
 * After moving, recomputes the source pile's new flute via SolverRemoveFlute,
 * then drains any suits that can now advance their foundation (busyAces).
 */
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

/*
 * Returns a local king-config bitmask of configurations under which the flute
 * of length `fluteLen` can legally be moved to `toPile`.
 *
 * Moving a flute requires free extra slots:
 *   - Pile-to-pile: fluteLen-1 free slots (interior cards park in extra).
 *   - Move to extra: fluteLen free slots.
 *   - Move to king pile: fluteLen free slots if the king has no dedicated empty
 *     pile yet, or fluteLen-1 free slots if the king's dedicated pile exists
 *     (the pile absorbs the flute boundary card, saving one extra slot).
 *
 * Flutes longer than 5 cannot be moved (only 4 extra slots exist).
 */
static uint16_t solverGetMovable(KingInfo *kingInfo, int shiftValue, int fluteLen, int toPile) {
    if (fluteLen > 5) {
        return 0;
    }
    if (toPile < KINGPILE) {
        /* move is pile to pile */
        return kingInfo->possibleKings[fluteLen - 1];
    } else if (toPile < EXTRA) {
        /* move is to king pile: need fluteLen extra slots if king not yet on pile,
         * or fluteLen-1 if king is already there (saves one intermediate move). */
        int kingOnPile = kingOnPileMap[toPile - KINGPILE] >> shiftValue;
        return kingInfo->possibleKings[fluteLen] | (kingInfo->possibleKings[fluteLen - 1] & kingOnPile);
    } else {
        return kingInfo->possibleKings[fluteLen];
    }
}

/*
 * Recursive solvability check.  Returns a local king-config bitmask indicating
 * which king configurations allow the game to be solved from this state.
 *
 * Base case: hash == 0 means all piles are empty (game solved); return 1.
 *
 * Otherwise, for each non-empty pile, determines the move destination and the
 * set of king configs under which the move is affordable.  Makes the move in a
 * copy of the game state (game[1]) and recurses.  The child's solvable bitmask
 * is translated back to the parent's configuration space via subsetTable, then
 * propagated through the component closure (if a config is solvable, all
 * configs in the same reachability component are also solvable).
 *
 * Results are memoised in hashmap keyed by game->hash.
 */
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

    /* allkings: configs feasible with 0 free extra slots (i.e., any space at all). */
    uint16_t allkings = kingInfo.possibleKings[0];
    /* component: closure of mutually reachable configurations. */
    uint16_t component = computeComponentKingBits(game);
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
        /* movable: configs where this move is affordable. */
        uint16_t movable = solverGetMovable(&kingInfo, closureInfo->shiftValue, fluteLen, toPile);
        assert((movable & ~allkings) == 0);
        if (movable & ~solvable) {
            /* At least one new config might become solvable; try the move. */
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
            /* Translate child's solvable bitmask to parent's config space, then
             * intersect with the configs for which this move was actually affordable. */
            movable &= subsetTable[closureInfos[game[1].freePiles].offset + recursiveSolvable] >> closureInfo->shiftValue;
            /* Propagate through the component: if any config in a component is
             * solvable, all configs in that component are solvable. */
            if (movable & component) {
                movable |= component;
            }
            solvable |= movable;
            if (solvable == allkings)
                break;
        }
    }
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

/*
 * Initialises the abstract game state from pile depths and a king bitmask.
 *
 * pilesking[0..9]: current depth of each pile (above-flute cards + 1; 0 if
 *   empty).  pilesking[10]: bitmask of suits whose king is already freed.
 *
 * For each pile, computes the flute: starting from the boundary card at
 * pos2card[pile][pileDepth-1], counts how many predecessor cards in the same
 * suit have already been freed from their original piles (card2depth >= current
 * pileDepth of their pile).  Those freed cards extend the flute.
 *
 * Also computes aces[] (highest foundation card per suit) by walking up each
 * suit's sequence until a still-in-pile card is found, and kings[] (first
 * un-freed card from the king end) similarly.
 *
 * usedSpace is computed as 52 minus all pile cards minus all foundation cards.
 */
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
            /* Walk down the suit sequence from the boundary card to find freed
             * predecessor cards that extend the flute. */
            int card = pos2card[i][game->pileDepth[i]-1] - 1;
            int flutelen = 1;
            while (card2depth[card] >= pilesking[card2pile[card]]) {
                flutelen++;
                card--;
            }
            game->pileFlute[i] = flutelen;
            /* Subtract all cards belonging to this pile: above-flute (depth)
             * plus flute interior (flutelen-1). */
            game->usedSpace -= depth + flutelen - 1;
        } else {
            game->pileFlute[i] = 1;
            game->freePiles++;
        }
    }
    for (i = 0; i < 4; i++) {
        int card = CARD(i, KING);
        int count = 0;

        /* Find the highest card of this suit already on the foundation. */
        int ace = CARD(i, ACE);
        while (ace <= card &&
               card2depth[ace] >= game->pileDepth[card2pile[ace]]) {
            ace++;
        }
        ace--;
        game->aces[i] = ace;
        game->usedSpace -= VALUE(ace);
        /* Find how many cards from the king end have been freed to king piles. */
        if (ace < card) {
            while (card2depth[card] >= game->pileDepth[card2pile[card]]) {
                count++;
                card--;
            }
        }
        game->kings[i] = card;
    }
}

/*
 * One-time initialisation: records the initial layout of the shuffled deck.
 *
 * cardshuffle[i] is a card number 1..52 (1=Ace of suit 0, 13=King of suit 0,
 * 14=Ace of suit 1, ...).  Cards are dealt column-by-column: card i goes to
 * pile (i % 10) at position (i / 10).  The last two cards (i=50,51) go to
 * extra and are not placed in any pile.
 */
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

/*
 * Entry point called from the web worker (or the standalone test harness).
 *
 * stacks[0..9]: current pile depths (pilesking format for SolverConvertFromPilesKings).
 * stacks[10]:   king bitmap where bit k SET means suit k's king is still in a
 *               regular pile (not yet freed); bit k UNSET means the king has
 *               been freed to a dedicated pile or extra cells.  XOR 0xf converts
 *               to the internal convention (bit k SET = king in extra slots).
 *
 * Converts the input to an abstract game state, runs the solvability check,
 * and writes the result to result[11]: SUCCESS (0) if solvable, NOMOVE (2) if not.
 * result[0..10] echoes the input stacks for the caller's reference.
 *
 * The king-config bitmask from the recursive check is queried at the grlex index
 * corresponding to the current king configuration derived from stacks[10].
 */
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
