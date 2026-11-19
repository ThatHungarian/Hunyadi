#include <algorithm>
#include <atomic>
#include <chrono>
#include <climits>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <memory>
#include <mutex>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

typedef uint64_t U64;
typedef uint16_t Move;

enum Color : int { WHITE = 0, BLACK = 1 };
enum PieceType : int { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING };
constexpr int NO_PIECE = 12;
constexpr int SQ_NONE = 64;

constexpr int MAX_PLY = 128;
constexpr int INF = 32000;
constexpr int MATE = 31000;
constexpr int MATE_IN_MAX = MATE - MAX_PLY;
constexpr int NO_EVAL = 32001;

constexpr Move NO_MOVE = 0;
constexpr Move NULL_MOVE = 0xFFFF;

constexpr U64 FILE_A = 0x0101010101010101ULL;
constexpr U64 FILE_H = FILE_A << 7;
constexpr U64 RANK_1 = 0xFFULL;
constexpr U64 RANK_2 = RANK_1 << 8;
constexpr U64 RANK_3 = RANK_1 << 16;
constexpr U64 RANK_6 = RANK_1 << 40;
constexpr U64 RANK_7 = RANK_1 << 48;
constexpr U64 RANK_8 = RANK_1 << 56;
constexpr U64 LIGHT_SQ = 0x55AA55AA55AA55AAULL;
constexpr U64 CENTER4 = (1ULL << 27) | (1ULL << 28) | (1ULL << 35) | (1ULL << 36);
constexpr U64 CENTER_EXT = 0x00003C3C3C3C0000ULL;

inline constexpr U64 bit(int s) { return 1ULL << s; }
inline int popcnt(U64 b) { return __builtin_popcountll(b); }
inline int lsb(U64 b) { return __builtin_ctzll(b); }
inline int msb(U64 b) { return 63 - __builtin_clzll(b); }
inline int popLsb(U64& b) { int s = lsb(b); b &= b - 1; return s; }
inline int fileOf(int s) { return s & 7; }
inline int rankOf(int s) { return s >> 3; }
inline int makePiece(int c, int t) { return c * 6 + t; }
inline int typeOf(int pc) { return pc >= 6 ? pc - 6 : pc; }
inline int colorOf(int pc) { return pc >= 6; }
inline int chebyshev(int a, int b) { return std::max(std::abs(fileOf(a) - fileOf(b)), std::abs(rankOf(a) - rankOf(b))); }

inline Move mk(int from, int to, int flag) { return (Move)(from | (to << 6) | (flag << 12)); }
inline int moveFrom(Move m) { return m & 63; }
inline int moveTo(Move m) { return (m >> 6) & 63; }
inline int moveFlag(Move m) { return m >> 12; }
inline bool isCapture(Move m) { return (m >> 12) & 4; }
inline bool isPromo(Move m) { return (m >> 12) & 8; }

static std::string moveStr(Move m) {
    if (m == NO_MOVE || m == NULL_MOVE) return "0000";
    std::string s;
    s += char('a' + fileOf(moveFrom(m)));
    s += char('1' + rankOf(moveFrom(m)));
    s += char('a' + fileOf(moveTo(m)));
    s += char('1' + rankOf(moveTo(m)));
    if (isPromo(m)) s += "nbrq"[moveFlag(m) & 3];
    return s;
}

U64 KnightAtt[64], KingAtt[64], PawnAtt[2][64];
U64 FileBB[8], RankBB[8], AdjFiles[8];
U64 ForwardRanks[2][8], ForwardFile[2][64], PassedMask[2][64];

struct Magic { U64 mask, magic; U64* attacks; unsigned shift; };
Magic RookMagics[64], BishopMagics[64];
U64 RookTable[0x19000], BishopTable[0x1480];

inline U64 rookAtt(int s, U64 occ) {
    const Magic& m = RookMagics[s];
    return m.attacks[((occ & m.mask) * m.magic) >> m.shift];
}
inline U64 bishopAtt(int s, U64 occ) {
    const Magic& m = BishopMagics[s];
    return m.attacks[((occ & m.mask) * m.magic) >> m.shift];
}
inline U64 queenAtt(int s, U64 occ) { return rookAtt(s, occ) | bishopAtt(s, occ); }

static U64 slidingAttack(int sq, U64 occ, bool rook) {
    static const int rd[4][2] = {{1, 0}, {-1, 0}, {0, 1}, {0, -1}};
    static const int bd[4][2] = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};
    const int(*d)[2] = rook ? rd : bd;
    U64 att = 0;
    for (int i = 0; i < 4; i++) {
        int f = fileOf(sq) + d[i][0], r = rankOf(sq) + d[i][1];
        while (f >= 0 && f < 8 && r >= 0 && r < 8) {
            U64 b = bit(r * 8 + f);
            att |= b;
            if (occ & b) break;
            f += d[i][0];
            r += d[i][1];
        }
    }
    return att;
}

struct PRNG {
    U64 s;
    explicit PRNG(U64 seed) : s(seed) {}
    U64 rand64() { s ^= s >> 12; s ^= s << 25; s ^= s >> 27; return s * 2685821657736338717ULL; }
    U64 sparse() { return rand64() & rand64() & rand64(); }
};

static void initMagics(bool rook, Magic* M, U64* table) {
    static const U64 seeds[8] = {728, 10316, 55013, 32803, 12281, 15100, 16645, 255};
    static U64 occupancy[4096], reference[4096];
    static int epoch[4096];
    std::memset(epoch, 0, sizeof(epoch));
    int cnt = 0, size = 0;
    for (int s = 0; s < 64; s++) {
        U64 edges = ((RANK_1 | RANK_8) & ~RankBB[rankOf(s)]) | ((FILE_A | FILE_H) & ~FileBB[fileOf(s)]);
        Magic& m = M[s];
        m.mask = slidingAttack(s, 0, rook) & ~edges;
        m.shift = 64 - popcnt(m.mask);
        m.attacks = (s == 0) ? table : M[s - 1].attacks + size;
        size = 0;
        U64 b = 0;
        do {
            occupancy[size] = b;
            reference[size] = slidingAttack(s, b, rook);
            size++;
            b = (b - m.mask) & m.mask;
        } while (b);
        PRNG rng(seeds[rankOf(s)]);
        for (int i = 0; i < size;) {
            for (m.magic = 0; popcnt((m.magic * m.mask) >> 56) < 6;) m.magic = rng.sparse();
            ++cnt;
            for (i = 0; i < size; i++) {
                unsigned idx = (unsigned)(((occupancy[i] & m.mask) * m.magic) >> m.shift);
                if (epoch[idx] < cnt) { epoch[idx] = cnt; m.attacks[idx] = reference[i]; }
                else if (m.attacks[idx] != reference[i]) break;
            }
        }
    }
}

U64 ZobPsq[12][64], ZobCastle[16], ZobEp[8], ZobSide;
uint8_t CastleMask[64];

static const int MG_VAL[6] = {82, 337, 365, 477, 1025, 0};
static const int EG_VAL[6] = {94, 281, 297, 512, 936, 0};
static const int PhaseInc[6] = {0, 1, 1, 2, 4, 0};
static const int SEE_VAL[6] = {100, 320, 330, 500, 900, 20000};

static const int MG_PST[6][64] = {
    {0, 0, 0, 0, 0, 0, 0, 0, 98, 134, 61, 95, 68, 126, 34, -11, -6, 7, 26, 31, 65, 56, 25, -20,
     -14, 13, 6, 21, 23, 12, 17, -23, -27, -2, -5, 12, 17, 6, 10, -25, -26, -4, -4, -10, 3, 3, 33, -12,
     -35, -1, -20, -23, -15, 24, 38, -22, 0, 0, 0, 0, 0, 0, 0, 0},
    {-167, -89, -34, -49, 61, -97, -15, -107, -73, -41, 72, 36, 23, 62, 7, -17, -47, 60, 37, 65, 84, 129, 73, 44,
     -9, 17, 19, 53, 37, 69, 18, 22, -13, 4, 16, 13, 28, 19, 21, -8, -23, -9, 12, 10, 19, 17, 25, -16,
     -29, -53, -12, -3, -1, 18, -14, -19, -105, -21, -58, -33, -17, -28, -19, -23},
    {-29, 4, -82, -37, -25, -42, 7, -8, -26, 16, -18, -13, 30, 59, 18, -47, -16, 37, 43, 40, 35, 50, 37, -2,
     -4, 5, 19, 50, 37, 37, 7, -2, -6, 13, 13, 26, 34, 12, 10, 4, 0, 15, 15, 15, 14, 27, 18, 10,
     4, 15, 16, 0, 7, 21, 33, 1, -33, -3, -14, -21, -13, -12, -39, -21},
    {32, 42, 32, 51, 63, 9, 31, 43, 27, 32, 58, 62, 80, 67, 26, 44, -5, 19, 26, 36, 17, 45, 61, 16,
     -24, -11, 7, 26, 24, 35, -8, -20, -36, -26, -12, -1, 9, -7, 6, -23, -45, -25, -16, -17, 3, 0, -5, -33,
     -44, -16, -20, -9, -1, 11, -6, -71, -19, -13, 1, 17, 16, 7, -37, -26},
    {-28, 0, 29, 12, 59, 44, 43, 45, -24, -39, -5, 1, -16, 57, 28, 54, -13, -17, 7, 8, 29, 56, 47, 57,
     -27, -27, -16, -16, -1, 17, -2, 1, -9, -26, -9, -10, -2, -4, 3, -3, -14, 2, -11, -2, -5, 2, 14, 5,
     -35, -8, 11, 2, 8, 15, -3, 1, -1, -18, -9, 10, -15, -25, -31, -50},
    {-65, 23, 16, -15, -56, -34, 2, 13, 29, -1, -20, -7, -8, -4, -38, -29, -9, 24, 2, -16, -20, 6, 22, -22,
     -17, -20, -12, -27, -30, -25, -14, -36, -49, -1, -27, -39, -46, -44, -33, -51, -14, -14, -22, -46, -44, -30, -15, -27,
     1, 7, -8, -64, -43, -16, 9, 8, -15, 36, 12, -54, 8, -28, 24, 14}};
static const int EG_PST[6][64] = {
    {0, 0, 0, 0, 0, 0, 0, 0, 178, 173, 158, 134, 147, 132, 165, 187, 94, 100, 85, 67, 56, 53, 82, 84,
     32, 24, 13, 5, -2, 4, 17, 17, 13, 9, -3, -7, -7, -8, 3, -1, 4, 7, -6, 1, 0, -5, -1, -8,
     13, 8, 8, 10, 13, 0, 2, -7, 0, 0, 0, 0, 0, 0, 0, 0},
    {-58, -38, -13, -28, -31, -27, -63, -99, -25, -8, -25, -2, -9, -25, -24, -52, -24, -20, 10, 9, -1, -9, -19, -41,
     -17, 3, 22, 22, 22, 11, 8, -18, -18, -6, 16, 25, 16, 17, 4, -18, -23, -3, -1, 15, 10, -3, -20, -22,
     -42, -20, -10, -5, -2, -20, -23, -44, -29, -51, -23, -15, -22, -18, -50, -64},
    {-14, -21, -11, -8, -7, -9, -17, -24, -8, -4, 7, -12, -3, -13, -4, -14, 2, -8, 0, -1, -2, 6, 0, 4,
     -3, 9, 12, 9, 14, 10, 3, 2, -6, 3, 13, 19, 7, 10, -3, -9, -12, -3, 8, 10, 13, 3, -7, -15,
     -14, -18, -7, -1, 4, -9, -15, -27, -23, -9, -23, -5, -9, -16, -5, -17},
    {13, 10, 18, 15, 12, 12, 8, 5, 11, 13, 13, 11, -3, 3, 8, 3, 7, 7, 7, 5, 4, -3, -5, -3,
     4, 3, 13, 1, 2, 1, -1, 2, 3, 5, 8, 4, -5, -6, -8, -11, -4, 0, -5, -1, -7, -12, -8, -16,
     -6, -6, 0, 2, -9, -9, -11, -3, -9, 2, 3, -1, -5, -13, 4, -20},
    {-9, 22, 22, 27, 27, 19, 10, 20, -17, 20, 32, 41, 58, 25, 30, 0, -20, 6, 9, 49, 47, 35, 19, 9,
     3, 22, 24, 45, 57, 40, 57, 36, -18, 28, 19, 47, 31, 34, 39, 23, -16, -27, 15, 6, 9, 17, 10, 5,
     -22, -23, -30, -16, -16, -23, -36, -32, -33, -28, -22, -43, -5, -32, -20, -41},
    {-74, -35, -18, -18, -11, 15, 4, -17, -12, 17, 14, 17, 17, 38, 23, 11, 10, 17, 23, 15, 20, 45, 44, 13,
     -8, 22, 24, 27, 26, 33, 26, 3, -18, -4, 21, 24, 27, 23, 9, -11, -19, -3, 11, 21, 23, 16, 7, -9,
     -27, -11, 4, 13, 14, 4, -5, -17, -53, -34, -21, -11, -28, -14, -24, -43}};

int MgTab[12][64], EgTab[12][64];
int LMRTable[64][64];

static void initTables() {
    for (int i = 0; i < 8; i++) {
        FileBB[i] = FILE_A << i;
        RankBB[i] = RANK_1 << (8 * i);
    }
    for (int i = 0; i < 8; i++) AdjFiles[i] = (i > 0 ? FileBB[i - 1] : 0) | (i < 7 ? FileBB[i + 1] : 0);
    for (int r = 0; r < 8; r++) {
        ForwardRanks[WHITE][r] = (r == 7) ? 0 : (~0ULL) << (8 * (r + 1));
        ForwardRanks[BLACK][r] = (1ULL << (8 * r)) - 1;
    }
    static const int kn[8][2] = {{1, 2}, {2, 1}, {2, -1}, {1, -2}, {-1, -2}, {-2, -1}, {-2, 1}, {-1, 2}};
    for (int s = 0; s < 64; s++) {
        int f = fileOf(s), r = rankOf(s);
        KnightAtt[s] = KingAtt[s] = PawnAtt[0][s] = PawnAtt[1][s] = 0;
        for (auto& d : kn) {
            int nf = f + d[0], nr = r + d[1];
            if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) KnightAtt[s] |= bit(nr * 8 + nf);
        }
        for (int df = -1; df <= 1; df++)
            for (int dr = -1; dr <= 1; dr++) {
                if (!df && !dr) continue;
                int nf = f + df, nr = r + dr;
                if (nf >= 0 && nf < 8 && nr >= 0 && nr < 8) KingAtt[s] |= bit(nr * 8 + nf);
            }
        for (int df = -1; df <= 1; df += 2) {
            int nf = f + df;
            if (nf < 0 || nf > 7) continue;
            if (r < 7) PawnAtt[WHITE][s] |= bit((r + 1) * 8 + nf);
            if (r > 0) PawnAtt[BLACK][s] |= bit((r - 1) * 8 + nf);
        }
        for (int c = 0; c < 2; c++) {
            ForwardFile[c][s] = FileBB[f] & ForwardRanks[c][r];
            PassedMask[c][s] = (FileBB[f] | AdjFiles[f]) & ForwardRanks[c][r];
        }
    }
    initMagics(true, RookMagics, RookTable);
    initMagics(false, BishopMagics, BishopTable);

    PRNG rng(1070372);
    for (int p = 0; p < 12; p++)
        for (int s = 0; s < 64; s++) ZobPsq[p][s] = rng.rand64();
    for (int i = 0; i < 8; i++) ZobEp[i] = rng.rand64();
    for (int i = 0; i < 16; i++) {
        ZobCastle[i] = 0;
        for (int b = 0; b < 4; b++)
            if (i & (1 << b)) ZobCastle[i] ^= (U64)(0x9E3779B97F4A7C15ULL * (b + 1)) ^ (U64)(0xC2B2AE3D27D4EB4FULL >> b);
    }
    ZobSide = rng.rand64();

    for (int s = 0; s < 64; s++) CastleMask[s] = 15;
    CastleMask[0] = 15 & ~2; CastleMask[4] = 15 & ~3; CastleMask[7] = 15 & ~1;
    CastleMask[56] = 15 & ~8; CastleMask[60] = 15 & ~12; CastleMask[63] = 15 & ~4;

    for (int t = 0; t < 6; t++)
        for (int s = 0; s < 64; s++) {
            MgTab[t][s] = MG_VAL[t] + MG_PST[t][s ^ 56];
            EgTab[t][s] = EG_VAL[t] + EG_PST[t][s ^ 56];
            MgTab[t + 6][s] = -(MG_VAL[t] + MG_PST[t][s]);
            EgTab[t + 6][s] = -(EG_VAL[t] + EG_PST[t][s]);
        }
    for (int d = 1; d < 64; d++)
        for (int m = 1; m < 64; m++) LMRTable[d][m] = (int)(0.77 + std::log((double)d) * std::log((double)m) / 2.36);
}

inline U64 pawnAttacksBB(U64 pawns, int c) {
    return c == WHITE ? (((pawns & ~FILE_A) << 7) | ((pawns & ~FILE_H) << 9))
                      : (((pawns & ~FILE_A) >> 9) | ((pawns & ~FILE_H) >> 7));
}

struct Position {
    U64 pieces[6];
    U64 colors[2];
    U64 occ;
    U64 key, pawnKey;
    int mg, eg, phase;
    uint8_t board[64];
    uint8_t stm, castling, epSq, halfmove;
    uint16_t fullmove;

    inline void put(int pc, int s) {
        U64 b = bit(s);
        int t = typeOf(pc);
        pieces[t] |= b; colors[colorOf(pc)] |= b; occ |= b;
        board[s] = (uint8_t)pc;
        key ^= ZobPsq[pc][s];
        mg += MgTab[pc][s]; eg += EgTab[pc][s]; phase += PhaseInc[t];
        if (t == PAWN) pawnKey ^= ZobPsq[pc][s];
    }
    inline void remove(int pc, int s) {
        U64 b = ~bit(s);
        int t = typeOf(pc);
        pieces[t] &= b; colors[colorOf(pc)] &= b; occ &= b;
        board[s] = NO_PIECE;
        key ^= ZobPsq[pc][s];
        mg -= MgTab[pc][s]; eg -= EgTab[pc][s]; phase -= PhaseInc[t];
        if (t == PAWN) pawnKey ^= ZobPsq[pc][s];
    }

    inline U64 attackersTo(int sq, U64 o) const {
        return (PawnAtt[BLACK][sq] & pieces[PAWN] & colors[WHITE]) | (PawnAtt[WHITE][sq] & pieces[PAWN] & colors[BLACK]) |
               (KnightAtt[sq] & pieces[KNIGHT]) | (KingAtt[sq] & pieces[KING]) |
               (rookAtt(sq, o) & (pieces[ROOK] | pieces[QUEEN])) | (bishopAtt(sq, o) & (pieces[BISHOP] | pieces[QUEEN]));
    }
    inline bool attackedBy(int sq, int by) const {
        U64 c = colors[by];
        return (PawnAtt[by ^ 1][sq] & pieces[PAWN] & c) || (KnightAtt[sq] & pieces[KNIGHT] & c) ||
               (KingAtt[sq] & pieces[KING] & c) || (bishopAtt(sq, occ) & (pieces[BISHOP] | pieces[QUEEN]) & c) ||
               (rookAtt(sq, occ) & (pieces[ROOK] | pieces[QUEEN]) & c);
    }
    inline int kingSq(int c) const { return lsb(pieces[KING] & colors[c]); }
    inline bool inCheck() const { return attackedBy(kingSq(stm), stm ^ 1); }
    inline bool leftInCheck() const { return attackedBy(kingSq(stm ^ 1), stm); } 
    inline bool hasNonPawn(int c) const {
        return (pieces[KNIGHT] | pieces[BISHOP] | pieces[ROOK] | pieces[QUEEN]) & colors[c];
    }

    void make(Move m) {
        int from = moveFrom(m), to = moveTo(m), flag = moveFlag(m);
        int us = stm, them = us ^ 1, pc = board[from];
        if (epSq != SQ_NONE) { key ^= ZobEp[epSq & 7]; epSq = SQ_NONE; }
        key ^= ZobCastle[castling];
        halfmove++;
        if (flag & 4) {
            int capSq = (flag == 5) ? to + (us == WHITE ? -8 : 8) : to;
            remove(board[capSq], capSq);
            halfmove = 0;
        }
        remove(pc, from);
        if (flag & 8) put(makePiece(us, (flag & 3) + KNIGHT), to);
        else put(pc, to);
        if (typeOf(pc) == PAWN) {
            halfmove = 0;
            if (flag == 1) {
                int e = (from + to) / 2;
                if (PawnAtt[us][e] & pieces[PAWN] & colors[them]) { epSq = (uint8_t)e; key ^= ZobEp[e & 7]; }
            }
        } else if (flag == 2) {
            int r = board[to + 1]; remove(r, to + 1); put(r, to - 1);
        } else if (flag == 3) {
            int r = board[to - 2]; remove(r, to - 2); put(r, to + 1);
        }
        castling &= CastleMask[from] & CastleMask[to];
        key ^= ZobCastle[castling];
        stm = (uint8_t)them;
        key ^= ZobSide;
        if (us == BLACK) fullmove++;
    }
    void makeNull() {
        if (epSq != SQ_NONE) { key ^= ZobEp[epSq & 7]; epSq = SQ_NONE; }
        stm ^= 1; key ^= ZobSide; halfmove++;
    }

    bool seeGE(Move m, int threshold) const {
        int from = moveFrom(m), to = moveTo(m), flag = moveFlag(m);
        int victim = (flag == 5) ? PAWN : (board[to] == NO_PIECE ? -1 : typeOf(board[to]));
        int swap = (victim < 0 ? 0 : SEE_VAL[victim]) - threshold;
        if (swap < 0) return false;
        swap = SEE_VAL[typeOf(board[from])] - swap;
        if (swap <= 0) return true;
        U64 o = occ ^ bit(from) ^ bit(to);
        if (flag == 5) o ^= bit(to + (stm == WHITE ? -8 : 8));
        int side = colorOf(board[from]);
        U64 att = attackersTo(to, o) & o;
        int res = 1;
        while (true) {
            side ^= 1;
            att &= o;
            U64 sa = att & colors[side];
            if (!sa) break;
            res ^= 1;
            U64 bb;
            if ((bb = sa & pieces[PAWN])) {
                if ((swap = SEE_VAL[PAWN] - swap) < res) break;
                o ^= bit(lsb(bb));
                att |= bishopAtt(to, o) & (pieces[BISHOP] | pieces[QUEEN]);
            } else if ((bb = sa & pieces[KNIGHT])) {
                if ((swap = SEE_VAL[KNIGHT] - swap) < res) break;
                o ^= bit(lsb(bb));
            } else if ((bb = sa & pieces[BISHOP])) {
                if ((swap = SEE_VAL[BISHOP] - swap) < res) break;
                o ^= bit(lsb(bb));
                att |= bishopAtt(to, o) & (pieces[BISHOP] | pieces[QUEEN]);
            } else if ((bb = sa & pieces[ROOK])) {
                if ((swap = SEE_VAL[ROOK] - swap) < res) break;
                o ^= bit(lsb(bb));
                att |= rookAtt(to, o) & (pieces[ROOK] | pieces[QUEEN]);
            } else if ((bb = sa & pieces[QUEEN])) {
                if ((swap = SEE_VAL[QUEEN] - swap) < res) break;
                o ^= bit(lsb(bb));
                att |= (bishopAtt(to, o) & (pieces[BISHOP] | pieces[QUEEN])) | (rookAtt(to, o) & (pieces[ROOK] | pieces[QUEEN]));
            } else {
                return (att & ~colors[side]) ? (res ^ 1) : res;
            }
        }
        return res != 0;
    }

    bool setFen(const std::string& fen);
    std::string fen() const;
    U64 computeKey() const;
};

static const char* PIECE_CHARS = "PNBRQKpnbrqk";

bool Position::setFen(const std::string& fenStr) {
    Position np;
    std::memset(&np, 0, sizeof(np));
    for (int i = 0; i < 64; i++) np.board[i] = NO_PIECE;
    np.epSq = SQ_NONE;
    std::istringstream ss(fenStr);
    std::string placement, side, castle, ep;
    int hm = 0, fm = 1;
    if (!(ss >> placement >> side)) return false;
    ss >> castle >> ep >> hm >> fm;
    int f = 0, r = 7;
    for (char ch : placement) {
        if (ch == '/') { if (f != 8) return false; f = 0; r--; if (r < 0) return false; }
        else if (ch >= '1' && ch <= '8') { f += ch - '0'; if (f > 8) return false; }
        else {
            const char* p = std::strchr(PIECE_CHARS, ch);
            if (!p || f > 7) return false;
            np.put((int)(p - PIECE_CHARS), r * 8 + f);
            f++;
        }
    }
    if (r != 0 || f != 8) return false;
    if (popcnt(np.pieces[KING] & np.colors[WHITE]) != 1 || popcnt(np.pieces[KING] & np.colors[BLACK]) != 1) return false;
    if (np.pieces[PAWN] & (RANK_1 | RANK_8)) return false;
    np.stm = (side == "b") ? BLACK : WHITE;
    if (np.stm == BLACK) np.key ^= ZobSide;
    np.castling = 0;
    if (castle != "-")
        for (char ch : castle) {
            if (ch == 'K' && np.board[4] == 5 && np.board[7] == 3) np.castling |= 1;
            else if (ch == 'Q' && np.board[4] == 5 && np.board[0] == 3) np.castling |= 2;
            else if (ch == 'k' && np.board[60] == 11 && np.board[63] == 9) np.castling |= 4;
            else if (ch == 'q' && np.board[60] == 11 && np.board[56] == 9) np.castling |= 8;
        }
    np.key ^= ZobCastle[np.castling];
    if (ep.size() == 2 && ep[0] >= 'a' && ep[0] <= 'h' && (ep[1] == '3' || ep[1] == '6')) {
        int e = (ep[1] - '1') * 8 + (ep[0] - 'a');
        int mover = np.stm; 
        if (PawnAtt[mover ^ 1][e] & np.pieces[PAWN] & np.colors[mover]) { np.epSq = (uint8_t)e; np.key ^= ZobEp[e & 7]; }
    }
    np.halfmove = (uint8_t)std::min(std::max(hm, 0), 255);
    np.fullmove = (uint16_t)std::max(fm, 1);
    if (np.attackedBy(np.kingSq(np.stm ^ 1), np.stm)) return false;
    *this = np;
    return true;
}

std::string Position::fen() const {
    std::string s;
    for (int r = 7; r >= 0; r--) {
        int e = 0;
        for (int f = 0; f < 8; f++) {
            int pc = board[r * 8 + f];
            if (pc == NO_PIECE) { e++; continue; }
            if (e) { s += char('0' + e); e = 0; }
            s += PIECE_CHARS[pc];
        }
        if (e) s += char('0' + e);
        if (r) s += '/';
    }
    s += stm == WHITE ? " w " : " b ";
    if (!castling) s += "-";
    else {
        if (castling & 1) s += 'K';
        if (castling & 2) s += 'Q';
        if (castling & 4) s += 'k';
        if (castling & 8) s += 'q';
    }
    s += " ";
    if (epSq == SQ_NONE) s += "-";
    else { s += char('a' + fileOf(epSq)); s += char('1' + rankOf(epSq)); }
    s += " " + std::to_string((int)halfmove) + " " + std::to_string((int)fullmove);
    return s;
}

U64 Position::computeKey() const {
    U64 k = 0;
    for (int s = 0; s < 64; s++)
        if (board[s] != NO_PIECE) k ^= ZobPsq[board[s]][s];
    if (stm == BLACK) k ^= ZobSide;
    k ^= ZobCastle[castling];
    if (epSq != SQ_NONE) k ^= ZobEp[epSq & 7];
    return k;
}

static bool insufficientMaterial(const Position& p) {
    if (p.pieces[PAWN] | p.pieces[ROOK] | p.pieces[QUEEN]) return false;
    int minors = popcnt(p.pieces[KNIGHT] | p.pieces[BISHOP]);
    if (minors <= 1) return true;
    if (!p.pieces[KNIGHT]) {
        U64 b = p.pieces[BISHOP];
        if (!(b & LIGHT_SQ) || !(b & ~LIGHT_SQ)) return true;
    }
    return false;
}

template <bool CAPS>
static int generate(const Position& p, Move* list) {
    int n = 0;
    const int us = p.stm, them = us ^ 1;
    const U64 own = p.colors[us], enemy = p.colors[them], occ = p.occ, empty = ~occ;
    const U64 pawns = p.pieces[PAWN] & own;
    const int up = us == WHITE ? 8 : -8;
    const U64 promoR = us == WHITE ? RANK_8 : RANK_1;
    const U64 third = us == WHITE ? RANK_3 : RANK_6;

    U64 single = (us == WHITE ? pawns << 8 : pawns >> 8) & empty;
    U64 dbl = (us == WHITE ? (single & third) << 8 : (single & third) >> 8) & empty;
    U64 promoS = single & promoR, quietS = single & ~promoR;
    U64 capL = (us == WHITE ? (pawns & ~FILE_A) << 7 : (pawns & ~FILE_A) >> 9) & enemy;
    U64 capR = (us == WHITE ? (pawns & ~FILE_H) << 9 : (pawns & ~FILE_H) >> 7) & enemy;
    const int dL = us == WHITE ? 7 : -9, dR = us == WHITE ? 9 : -7;

    while (promoS) {
        int to = popLsb(promoS);
        list[n++] = mk(to - up, to, 11);
        if (!CAPS) { list[n++] = mk(to - up, to, 10); list[n++] = mk(to - up, to, 9); list[n++] = mk(to - up, to, 8); }
    }
    if (!CAPS) {
        while (quietS) { int to = popLsb(quietS); list[n++] = mk(to - up, to, 0); }
        while (dbl) { int to = popLsb(dbl); list[n++] = mk(to - 2 * up, to, 1); }
    }
    for (int side = 0; side < 2; side++) {
        U64& c = side == 0 ? capL : capR;
        int d = side == 0 ? dL : dR;
        U64 pc = c & promoR;
        c &= ~promoR;
        while (pc) {
            int to = popLsb(pc);
            list[n++] = mk(to - d, to, 15);
            if (!CAPS) { list[n++] = mk(to - d, to, 14); list[n++] = mk(to - d, to, 13); list[n++] = mk(to - d, to, 12); }
        }
        while (c) { int to = popLsb(c); list[n++] = mk(to - d, to, 4); }
    }
    if (p.epSq != SQ_NONE) {
        U64 a = PawnAtt[them][p.epSq] & pawns;
        while (a) list[n++] = mk(popLsb(a), p.epSq, 5);
    }

    const U64 targets = CAPS ? enemy : ~own;
    U64 bb = p.pieces[KNIGHT] & own;
    while (bb) {
        int s = popLsb(bb);
        U64 a = KnightAtt[s] & targets;
        while (a) { int t = popLsb(a); list[n++] = mk(s, t, (enemy >> t) & 1 ? 4 : 0); }
    }
    bb = p.pieces[BISHOP] & own;
    while (bb) {
        int s = popLsb(bb);
        U64 a = bishopAtt(s, occ) & targets;
        while (a) { int t = popLsb(a); list[n++] = mk(s, t, (enemy >> t) & 1 ? 4 : 0); }
    }
    bb = p.pieces[ROOK] & own;
    while (bb) {
        int s = popLsb(bb);
        U64 a = rookAtt(s, occ) & targets;
        while (a) { int t = popLsb(a); list[n++] = mk(s, t, (enemy >> t) & 1 ? 4 : 0); }
    }
    bb = p.pieces[QUEEN] & own;
    while (bb) {
        int s = popLsb(bb);
        U64 a = queenAtt(s, occ) & targets;
        while (a) { int t = popLsb(a); list[n++] = mk(s, t, (enemy >> t) & 1 ? 4 : 0); }
    }
    {
        int s = lsb(p.pieces[KING] & own);
        U64 a = KingAtt[s] & targets;
        while (a) { int t = popLsb(a); list[n++] = mk(s, t, (enemy >> t) & 1 ? 4 : 0); }
        if (!CAPS && p.castling) {
            if (us == WHITE) {
                if ((p.castling & 1) && !(occ & (bit(5) | bit(6))) && !p.attackedBy(4, BLACK) && !p.attackedBy(5, BLACK) && !p.attackedBy(6, BLACK))
                    list[n++] = mk(4, 6, 2);
                if ((p.castling & 2) && !(occ & (bit(1) | bit(2) | bit(3))) && !p.attackedBy(4, BLACK) && !p.attackedBy(3, BLACK) && !p.attackedBy(2, BLACK))
                    list[n++] = mk(4, 2, 3);
            } else {
                if ((p.castling & 4) && !(occ & (bit(61) | bit(62))) && !p.attackedBy(60, WHITE) && !p.attackedBy(61, WHITE) && !p.attackedBy(62, WHITE))
                    list[n++] = mk(60, 62, 2);
                if ((p.castling & 8) && !(occ & (bit(57) | bit(58) | bit(59))) && !p.attackedBy(60, WHITE) && !p.attackedBy(59, WHITE) && !p.attackedBy(58, WHITE))
                    list[n++] = mk(60, 58, 3);
            }
        }
    }
    return n;
}

static Move parseMove(const Position& p, const std::string& s) {
    Move mv[256];
    int n = generate<false>(p, mv);
    for (int i = 0; i < n; i++)
        if (moveStr(mv[i]) == s) {
            Position np = p;
            np.make(mv[i]);
            if (!np.leftInCheck()) return mv[i];
        }
    return NO_MOVE;
}

static U64 perft(const Position& p, int depth) {
    Move mv[256];
    int n = generate<false>(p, mv);
    U64 total = 0;
    for (int i = 0; i < n; i++) {
        Position np = p;
        np.make(mv[i]);
        if (np.leftInCheck()) continue;
        total += depth <= 1 ? 1 : perft(np, depth - 1);
    }
    return total;
}

static std::mutex g_outMutex;
static void out(const std::string& s) {
    std::lock_guard<std::mutex> lk(g_outMutex);
    std::fputs(s.c_str(), stdout);
    std::fputc('\n', stdout);
    std::fflush(stdout);
}
static inline int64_t nowMs() {
    return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

struct SearchLimits {
    int64_t time[2] = {0, 0}, inc[2] = {0, 0}, movetime = 0;
    int movestogo = 0, depth = 0;
    int64_t nodes = 0;
    bool infinite = false, ponder = false, timed = false;
    std::vector<Move> searchmoves;
};
static SearchLimits g_lim;
static std::atomic<bool> g_stop{false};
static std::atomic<bool> g_pondering{false};
static std::atomic<int64_t> g_start{0};
static int64_t g_optimum = 0, g_maxTime = 0;
static int g_threads = 1, g_moveOverhead = 20;
static bool g_ponderOpt = false;

enum Bound { BOUND_NONE = 0, BOUND_LOWER = 1, BOUND_UPPER = 2, BOUND_EXACT = 3 };

struct TTData { Move move; int score, eval, depth, bound; };

struct TTEntry { std::atomic<U64> keyx, data; };
struct alignas(64) TTBucket { TTEntry e[4]; };

struct TranspositionTable {
    TTBucket* table = nullptr;
    void* raw = nullptr;
    size_t nb = 0;
    uint8_t gen = 0;

    ~TranspositionTable() { std::free(raw); }
    void resize(size_t mb) {
        std::free(raw);
        raw = nullptr; table = nullptr; nb = 0;
        while (mb >= 1) {
            size_t n = mb * 1024 * 1024 / sizeof(TTBucket);
            raw = std::calloc(n * sizeof(TTBucket) + 64, 1);
            if (raw) {
                table = (TTBucket*)(((uintptr_t)raw + 63) & ~(uintptr_t)63);
                nb = n;
                return;
            }
            mb /= 2;
        }
        raw = std::calloc(sizeof(TTBucket) * 2 + 64, 1);
        table = (TTBucket*)(((uintptr_t)raw + 63) & ~(uintptr_t)63);
        nb = 1;
    }
    void clear() { if (table) std::memset((void*)table, 0, nb * sizeof(TTBucket)); gen = 0; }
    void newSearch() { gen = (gen + 1) & 63; }
    inline TTBucket& bucket(U64 key) const { return table[(size_t)(((unsigned __int128)key * nb) >> 64)]; }

    static inline int toTT(int s, int ply) { return s >= MATE_IN_MAX ? s + ply : (s <= -MATE_IN_MAX ? s - ply : s); }
    static inline int fromTT(int s, int ply) { return s >= MATE_IN_MAX ? s - ply : (s <= -MATE_IN_MAX ? s + ply : s); }

    bool probe(U64 key, TTData& d, int ply) const {
        TTBucket& b = bucket(key);
        for (int i = 0; i < 4; i++) {
            U64 dt = b.e[i].data.load(std::memory_order_relaxed);
            U64 kx = b.e[i].keyx.load(std::memory_order_relaxed);
            if (dt && (kx ^ dt) == key) {
                d.move = (Move)(dt & 0xFFFF);
                d.score = fromTT((int16_t)((dt >> 16) & 0xFFFF), ply);
                d.eval = (int16_t)((dt >> 32) & 0xFFFF);
                d.depth = (int)((dt >> 48) & 0xFF);
                d.bound = (int)((dt >> 56) & 3);
                return true;
            }
        }
        return false;
    }
    void store(U64 key, Move m, int score, int eval, int depth, int bound, int ply) {
        TTBucket& b = bucket(key);
        int rep = 0, worst = INT_MAX;
        for (int i = 0; i < 4; i++) {
            U64 dt = b.e[i].data.load(std::memory_order_relaxed);
            U64 kx = b.e[i].keyx.load(std::memory_order_relaxed);
            if (dt && (kx ^ dt) == key) {
                Move old = (Move)(dt & 0xFFFF);
                int od = (int)((dt >> 48) & 0xFF);
                int ogen = (int)(dt >> 58);
                if (!m) m = old;
                if (bound != BOUND_EXACT && depth < od - 3 && ogen == gen) return;
                rep = i;
                worst = INT_MIN;
                break;
            }
            int val;
            if (!dt) val = -100000;
            else {
                int age = (gen - (int)(dt >> 58)) & 63;
                val = (int)((dt >> 48) & 0xFF) - 8 * age;
            }
            if (val < worst) { worst = val; rep = i; }
        }
        U64 dt = (U64)m | ((U64)(uint16_t)(int16_t)toTT(score, ply) << 16) | ((U64)(uint16_t)(int16_t)eval << 32) |
                 ((U64)(uint8_t)depth << 48) | ((U64)(((gen << 2) | bound) & 0xFF) << 56);
        b.e[rep].data.store(dt, std::memory_order_relaxed);
        b.e[rep].keyx.store(key ^ dt, std::memory_order_relaxed);
    }
    int hashfull() const {
        int cnt = 0;
        size_t n = std::min<size_t>(nb, 250);
        for (size_t i = 0; i < n; i++)
            for (int j = 0; j < 4; j++) {
                U64 dt = table[i].e[j].data.load(std::memory_order_relaxed);
                if (dt && (int)(dt >> 58) == gen) cnt++;
            }
        return (int)(cnt * 1000 / (n * 4));
    }
};
static TranspositionTable TT;
static const int PassMg[8] = {0, 4, 8, 15, 30, 55, 90, 0};
static const int PassEg[8] = {0, 10, 18, 35, 65, 110, 170, 0};
static const int ConnBonus[8] = {0, 2, 4, 7, 14, 26, 45, 0};
constexpr int TEMPO = 10;
constexpr int PAWN_TABLE_SIZE = 8192;

struct PawnEntry { U64 key; U64 passed[2]; int16_t mg, eg; };

static void evalPawns(const Position& p, PawnEntry& pe) {
    pe.key = p.pawnKey;
    pe.passed[0] = pe.passed[1] = 0;
    int mg = 0, eg = 0;
    for (int c = 0; c < 2; c++) {
        int sg = c == WHITE ? 1 : -1;
        U64 own = p.pieces[PAWN] & p.colors[c], opp = p.pieces[PAWN] & p.colors[c ^ 1];
        U64 bb = own;
        int m = 0, e = 0;
        while (bb) {
            int s = popLsb(bb), f = fileOf(s), r = rankOf(s);
            int rr = c == WHITE ? r : 7 - r;
            int stop = s + (c == WHITE ? 8 : -8);
            bool passed = !(PassedMask[c][s] & opp);
            bool doubled = (ForwardFile[c][s] & own) != 0;
            bool isolated = !(AdjFiles[f] & own);
            bool supported = (PawnAtt[c ^ 1][s] & own) != 0;
            bool phalanx = (f > 0 && (own & bit(s - 1))) || (f < 7 && (own & bit(s + 1)));
            bool backward = false;
            if (!isolated && !supported && !phalanx && !passed) {
                U64 behind = AdjFiles[f] & own & ~ForwardRanks[c][r];
                if (!behind && stop >= 0 && stop < 64 && (PawnAtt[c][stop] & opp)) backward = true;
            }
            if (passed && !doubled) { m += PassMg[rr]; e += PassEg[rr]; pe.passed[c] |= bit(s); }
            if (doubled) { m -= 8; e -= 20; }
            if (isolated) { m -= 10; e -= 14; }
            if (backward) { m -= 8; e -= 10; }
            if (supported || phalanx) {
                int cb = ConnBonus[rr];
                m += cb * (2 * (int)phalanx + (int)supported) / 2;
                e += cb * ((int)phalanx + (int)supported) / 2;
            }
        }
        mg += sg * m;
        eg += sg * e;
    }
    pe.mg = (int16_t)mg;
    pe.eg = (int16_t)eg;
}

struct StackEntry { Move move; int pt; int staticEval; };

struct Searcher {
    int id = 0;
    Position pos[MAX_PLY + 4];
    StackEntry ssBase[MAX_PLY + 8];
    StackEntry* ss = ssBase + 2;
    std::vector<U64> keys;
    int base = 0;
    Move killers[MAX_PLY + 4][2];
    int16_t history[2][64][64];
    std::vector<int16_t> contHist; 
    Move counters[769];
    Move pv[MAX_PLY + 4][MAX_PLY + 4];
    int pvLen[MAX_PLY + 4];
    uint64_t nodes = 0;
    std::atomic<uint64_t> nodesShared{0};
    int seldepth = 0;
    int completedDepth = 0;
    Move bestMove = NO_MOVE, ponderMove = NO_MOVE;
    int bestScore = 0;
    std::vector<PawnEntry> pawnTable;

    Searcher() : contHist(769 * 768, 0), pawnTable(PAWN_TABLE_SIZE) { clearAll(); }

    void clearAll() {
        std::memset(history, 0, sizeof(history));
        std::fill(contHist.begin(), contHist.end(), 0);
        std::memset(counters, 0, sizeof(counters));
        std::memset(killers, 0, sizeof(killers));
        for (auto& e : pawnTable) { e.key = 1; e.mg = e.eg = 0; e.passed[0] = e.passed[1] = 0; }
    }

    void setup(const Position& root, const std::vector<U64>& gameKeys) {
        pos[0] = root;
        keys = gameKeys;
        base = (int)keys.size() - 1;
        keys.resize(base + MAX_PLY + 8, 0);
        std::memset(killers, 0, sizeof(killers));
        for (int i = 0; i < MAX_PLY + 8; i++) { ssBase[i].move = NO_MOVE; ssBase[i].pt = 768; ssBase[i].staticEval = NO_EVAL; }
        nodes = 0; nodesShared = 0; seldepth = 0; completedDepth = 0;
        bestMove = ponderMove = NO_MOVE; bestScore = 0;
    }

    int evaluate(const Position& p);

    inline bool stopped() const { return g_stop.load(std::memory_order_relaxed); }

    void checkLimits() {
        nodesShared.store(nodes, std::memory_order_relaxed);
        if (id != 0) return;
        if (g_lim.nodes && (int64_t)nodes >= g_lim.nodes && completedDepth >= 1) { g_stop = true; return; }
        if (completedDepth < 1) return;
        if (g_pondering.load() || g_lim.infinite || !g_lim.timed) return;
        if (nowMs() - g_start.load() >= g_maxTime) g_stop = true;
    }

    bool isDraw(const Position& p, int ply) const {
        if (insufficientMaterial(p)) return true;
        if (p.halfmove >= 100) return true;
        int idx = base + ply;
        int cnt = 0;
        int lim = std::min<int>(p.halfmove, idx);
        for (int i = 4; i <= lim; i += 2)
            if (keys[idx - i] == p.key) {
                if (i <= ply) return true;
                if (++cnt >= 2) return true;
            }
        return false;
    }

    inline int quietScore(int us, Move m, int piece, int ply) const {
        int to = moveTo(m), from = moveFrom(m);
        int pt = piece * 64 + to;
        return history[us][from][to] + contHist[ss[ply - 1].pt * 768 + pt] + contHist[ss[ply - 2].pt * 768 + pt];
    }
    static inline void updHist(int16_t& h, int bonus) {
        int v = h;
        v += bonus - v * std::abs(bonus) / 16384;
        h = (int16_t)v;
    }
    void updateQuietStats(const Position& p, int ply, Move best, const Move* tried, int nt, int depth) {
        int us = p.stm;
        if (killers[ply][0] != best) { killers[ply][1] = killers[ply][0]; killers[ply][0] = best; }
        counters[ss[ply - 1].pt] = best;
        int bonus = std::min(2400, depth * depth * 32 + 16);
        auto upd = [&](Move m, int b) {
            int piece = p.board[moveFrom(m)];
            int pt = piece * 64 + moveTo(m);
            updHist(history[us][moveFrom(m)][moveTo(m)], b);
            updHist(contHist[ss[ply - 1].pt * 768 + pt], b);
            updHist(contHist[ss[ply - 2].pt * 768 + pt], b);
        };
        upd(best, bonus);
        for (int i = 0; i < nt; i++) upd(tried[i], -bonus);
    }

    void scoreMoves(const Position& p, const Move* mv, int* sc, int n, Move ttMove, int ply) {
        int us = p.stm;
        Move counter = counters[ss[ply - 1].pt];
        for (int i = 0; i < n; i++) {
            Move m = mv[i];
            int flag = moveFlag(m);
            if (m == ttMove) { sc[i] = 1 << 30; continue; }
            if (flag & 8) {
                sc[i] = ((flag & 3) == 3 ? 1900000 : -3000000);
                if (flag & 4) sc[i] += 10 * SEE_VAL[typeOf(p.board[moveTo(m)])];
            } else if (flag & 4) {
                int victim = flag == 5 ? PAWN : typeOf(p.board[moveTo(m)]);
                int att = typeOf(p.board[moveFrom(m)]);
                int s = 10 * SEE_VAL[victim] - att;
                sc[i] = s + (p.seeGE(m, 0) ? 2000000 : -2000000);
            } else {
                if (m == killers[ply][0]) sc[i] = 1500000;
                else if (m == killers[ply][1]) sc[i] = 1400000;
                else if (m == counter) sc[i] = 1300000;
                else sc[i] = quietScore(us, m, p.board[moveFrom(m)], ply);
            }
        }
    }

    template <bool PV> int search(int alpha, int beta, int depth, int ply);
    template <bool PV> int qsearch(int alpha, int beta, int ply);
    void iterate();
};

int Searcher::evaluate(const Position& p) {
    PawnEntry& pe = pawnTable[p.pawnKey & (PAWN_TABLE_SIZE - 1)];
    if (pe.key != p.pawnKey) evalPawns(p, pe);
    int mg = p.mg + pe.mg, eg = p.eg + pe.eg;
    const U64 occ = p.occ;
    int units[2] = {0, 0}, attackers[2] = {0, 0};
    int kSq[2] = {p.kingSq(0), p.kingSq(1)};

    for (int c = 0; c < 2; c++) {
        const int them = c ^ 1, sg = c == WHITE ? 1 : -1;
        const U64 own = p.colors[c], opp = p.colors[them];
        const U64 ownP = p.pieces[PAWN] & own, oppP = p.pieces[PAWN] & opp;
        const U64 oppPawnAtt = pawnAttacksBB(oppP, them);
        const U64 area = ~(ownP | (p.pieces[KING] & own)) & ~oppPawnAtt;
        U64 zone = KingAtt[kSq[them]] | bit(kSq[them]);
        zone |= (them == WHITE ? zone << 8 : zone >> 8);
        int m = 0, e = 0;

        U64 bb = p.pieces[KNIGHT] & own;
        while (bb) {
            int s = popLsb(bb);
            U64 a = KnightAtt[s];
            int mob = popcnt(a & area);
            m += (mob - 4) * 4; e += (mob - 4) * 3;
            int rr = c == WHITE ? rankOf(s) : 7 - rankOf(s);
            if (rr >= 3 && rr <= 5 && (PawnAtt[them][s] & ownP) && !(PassedMask[c][s] & ~FileBB[fileOf(s)] & oppP)) { m += 22; e += 12; }
            if (a & zone) { attackers[c]++; units[c] += 2 + popcnt(a & zone); }
        }
        int bishops = 0;
        bb = p.pieces[BISHOP] & own;
        while (bb) {
            int s = popLsb(bb);
            bishops++;
            U64 a = bishopAtt(s, occ);
            int mob = popcnt(a & area);
            m += (mob - 6) * 4; e += (mob - 6) * 4;
            int same = popcnt(ownP & ((bit(s) & LIGHT_SQ) ? LIGHT_SQ : ~LIGHT_SQ));
            m -= same * 2; e -= same * 3;
            if (a & zone) { attackers[c]++; units[c] += 2 + popcnt(a & zone); }
        }
        if (bishops >= 2) { m += 28; e += 48; }
        bb = p.pieces[ROOK] & own;
        U64 rq = (p.pieces[ROOK] | p.pieces[QUEEN]) & own;
        while (bb) {
            int s = popLsb(bb);
            U64 a = rookAtt(s, occ ^ rq);
            int mob = popcnt(a & area);
            m += (mob - 7) * 2; e += (mob - 7) * 4;
            int f = fileOf(s);
            if (!(FileBB[f] & ownP)) {
                if (!(FileBB[f] & oppP)) { m += 25; e += 10; }
                else { m += 12; e += 8; }
            }
            int rr = c == WHITE ? rankOf(s) : 7 - rankOf(s);
            if (rr == 6 && ((c == WHITE ? rankOf(kSq[them]) == 7 : rankOf(kSq[them]) == 0) || (oppP & RankBB[rankOf(s)]))) { m += 15; e += 25; }
            if (a & zone) { attackers[c]++; units[c] += 3 + popcnt(a & zone); }
        }
        bb = p.pieces[QUEEN] & own;
        while (bb) {
            int s = popLsb(bb);
            U64 a = rookAtt(s, occ) | bishopAtt(s, occ);
            int mob = popcnt(a & area);
            m += (mob - 13); e += (mob - 13) * 2;
            if (a & zone) { attackers[c]++; units[c] += 5 + popcnt(a & zone); }
        }
        U64 pa = pawnAttacksBB(ownP, c);
        U64 nonPawn = opp & ~p.pieces[PAWN] & ~p.pieces[KING];
        int th = popcnt(pa & nonPawn);
        m += th * 22; e += th * 14;
        m += popcnt(pa & CENTER_EXT) * 3;
        m += popcnt(pa & CENTER4) * 2;

        {
            int ks = kSq[c], kf = fileOf(ks), kr = rankOf(ks);
            int cf = std::min(std::max(kf, 1), 6);
            for (int f = cf - 1; f <= cf + 1; f++) {
                U64 fwd = ForwardRanks[c][kr] & FileBB[f];
                U64 mine = fwd & ownP;
                if (mine) {
                    int ps = c == WHITE ? lsb(mine) : msb(mine);
                    int d = std::abs(rankOf(ps) - kr);
                    m += d == 1 ? 12 : (d == 2 ? 7 : 3);
                } else {
                    m -= 18;
                    if (!(FileBB[f] & oppP)) m -= 10;
                }
                U64 theirs = fwd & oppP;
                if (theirs) {
                    int ps = c == WHITE ? lsb(theirs) : msb(theirs);
                    int d = std::abs(rankOf(ps) - kr);
                    if (d <= 3) m -= (4 - d) * 5;
                }
            }
        }
        mg += sg * m;
        eg += sg * e;
    }
    for (int c = 0; c < 2; c++) {
        if (attackers[c] >= 2 || (attackers[c] == 1 && (p.pieces[QUEEN] & p.colors[c]))) {
            int pen = std::min(units[c] * units[c] / 4, 400);
            if (!(p.pieces[QUEEN] & p.colors[c])) pen /= 2;
            mg += (c == WHITE ? 1 : -1) * pen;
        }
    }
    for (int c = 0; c < 2; c++) {
        U64 pp = pe.passed[c];
        int sg = c == WHITE ? 1 : -1;
        while (pp) {
            int s = popLsb(pp);
            int rr = c == WHITE ? rankOf(s) : 7 - rankOf(s);
            int stop = s + (c == WHITE ? 8 : -8);
            if (rr >= 2) {
                int v = (chebyshev(kSq[c ^ 1], stop) * 5 - chebyshev(kSq[c], stop) * 2) * (rr - 1) / 3;
                eg += sg * v;
            }
            if (occ & bit(stop)) eg -= sg * PassEg[rr] / 5;
        }
    }
    {
        int npm[2];
        for (int c = 0; c < 2; c++)
            npm[c] = popcnt(p.pieces[KNIGHT] & p.colors[c]) * 320 + popcnt(p.pieces[BISHOP] & p.colors[c]) * 330 +
                     popcnt(p.pieces[ROOK] & p.colors[c]) * 500 + popcnt(p.pieces[QUEEN] & p.colors[c]) * 900;
        int strong = eg > 0 ? WHITE : BLACK;
        if (!(p.pieces[PAWN] & p.colors[strong])) {
            if (npm[strong] - npm[strong ^ 1] <= 330) eg /= 8;
        } else if (popcnt(p.pieces[BISHOP]) == 2 && popcnt(p.pieces[BISHOP] & p.colors[WHITE]) == 1 &&
                   !(p.pieces[KNIGHT] | p.pieces[ROOK] | p.pieces[QUEEN])) {
            U64 wb = p.pieces[BISHOP] & p.colors[WHITE], bbp = p.pieces[BISHOP] & p.colors[BLACK];
            if (((wb & LIGHT_SQ) != 0) != ((bbp & LIGHT_SQ) != 0)) eg /= 2;
        }
    }
    int ph = std::min(std::max(p.phase, 0), 24);
    int score = (mg * ph + eg * (24 - ph)) / 24;
    score = score * (200 - std::min<int>(p.halfmove, 100)) / 200;
    if (p.stm == BLACK) score = -score;
    return score + TEMPO;
}

template <bool PV>
int Searcher::qsearch(int alpha, int beta, int ply) {
    Position& p = pos[ply];
    pvLen[ply] = ply;
    nodes++;
    if (ply > seldepth) seldepth = ply;
    if ((nodes & 2047) == 0) checkLimits();
    if (stopped()) return 0;
    if (isDraw(p, ply)) return 0;
    if (ply >= MAX_PLY - 1) return evaluate(p);

    const bool inCheck = p.inCheck();
    TTData tt;
    bool ttHit = TT.probe(p.key, tt, ply);
    Move ttMove = ttHit ? tt.move : NO_MOVE;
    if (!PV && ttHit && p.halfmove < 90 &&
        (tt.bound == BOUND_EXACT || (tt.bound == BOUND_LOWER && tt.score >= beta) || (tt.bound == BOUND_UPPER && tt.score <= alpha)))
        return tt.score;

    int best, staticEval = NO_EVAL;
    const int origAlpha = alpha;
    if (inCheck) best = -INF;
    else {
        staticEval = (ttHit && tt.eval != NO_EVAL) ? tt.eval : evaluate(p);
        best = staticEval;
        if (ttHit && std::abs(tt.score) < MATE_IN_MAX &&
            (tt.bound == BOUND_EXACT || (tt.bound == BOUND_LOWER && tt.score > best) || (tt.bound == BOUND_UPPER && tt.score < best)))
            best = tt.score;
        if (best >= beta) {
            if (!ttHit) TT.store(p.key, NO_MOVE, best, staticEval, 0, BOUND_LOWER, ply);
            return best;
        }
        if (best > alpha) alpha = best;
    }

    Move mv[256];
    int sc[256];
    int n = inCheck ? generate<false>(p, mv) : generate<true>(p, mv);
    scoreMoves(p, mv, sc, n, ttMove, ply);
    Move bestMove = NO_MOVE;
    int moveCount = 0;
    for (int i = 0; i < n; i++) {
        int bi = i;
        for (int j = i + 1; j < n; j++) if (sc[j] > sc[bi]) bi = j;
        std::swap(mv[i], mv[bi]); std::swap(sc[i], sc[bi]);
        Move m = mv[i];
        if (!inCheck) {
            if (!isPromo(m)) {
                int victim = moveFlag(m) == 5 ? PAWN : typeOf(p.board[moveTo(m)]);
                if (staticEval + SEE_VAL[victim] + 200 < alpha) continue;
            }
            if (!p.seeGE(m, 0)) continue;
        }
        Position& np = pos[ply + 1];
        np = p;
        np.make(m);
        if (np.leftInCheck()) continue;
        moveCount++;
        keys[base + ply + 1] = np.key;
        ss[ply].move = m;
        ss[ply].pt = p.board[moveFrom(m)] * 64 + moveTo(m);
        int score = -qsearch<PV>(-beta, -alpha, ply + 1);
        if (stopped()) return 0;
        if (score > best) {
            best = score;
            if (score > alpha) {
                bestMove = m;
                alpha = score;
                if (PV) {
                    pv[ply][ply] = m;
                    for (int j = ply + 1; j < pvLen[ply + 1]; j++) pv[ply][j] = pv[ply + 1][j];
                    pvLen[ply] = std::max(pvLen[ply + 1], ply + 1);
                }
                if (alpha >= beta) break;
            }
        }
    }
    if (inCheck && moveCount == 0) return -MATE + ply;
    int bound = best >= beta ? BOUND_LOWER : ((PV && bestMove) ? BOUND_EXACT : BOUND_UPPER);
    (void)origAlpha;
    TT.store(p.key, bestMove, best, staticEval, 0, bound, ply);
    return best;
}

template <bool PV>
int Searcher::search(int alpha, int beta, int depth, int ply) {
    const bool root = ply == 0;
    Position& p = pos[ply];
    pvLen[ply] = ply;
    if (depth <= 0) return qsearch<PV>(alpha, beta, ply);

    nodes++;
    if (ply > seldepth) seldepth = ply;
    if ((nodes & 2047) == 0) checkLimits();
    if (stopped()) return 0;

    const bool inCheck = p.inCheck();
    if (!root) {
        if (isDraw(p, ply)) return 0;
        if (ply >= MAX_PLY - 1) return inCheck ? 0 : evaluate(p);
        alpha = std::max(alpha, -MATE + ply);
        beta = std::min(beta, MATE - ply - 1);
        if (alpha >= beta) return alpha;
    }
    const int us = p.stm;
    killers[ply + 1][0] = killers[ply + 1][1] = NO_MOVE;

    TTData tt;
    bool ttHit = TT.probe(p.key, tt, ply);
    Move ttMove = ttHit ? tt.move : NO_MOVE;
    if (!PV && ttHit && tt.depth >= depth && p.halfmove < 90 &&
        (tt.bound == BOUND_EXACT || (tt.bound == BOUND_LOWER && tt.score >= beta) || (tt.bound == BOUND_UPPER && tt.score <= alpha)))
        return tt.score;

    int eval = NO_EVAL;
    bool improving = false;
    if (inCheck) {
        ss[ply].staticEval = NO_EVAL;
    } else {
        eval = (ttHit && tt.eval != NO_EVAL) ? tt.eval : evaluate(p);
        ss[ply].staticEval = eval;
        if (ttHit && std::abs(tt.score) < MATE_IN_MAX &&
            (tt.bound == BOUND_EXACT || (tt.bound == BOUND_LOWER && tt.score > eval) || (tt.bound == BOUND_UPPER && tt.score < eval)))
            eval = tt.score;
        improving = ply >= 2 && ss[ply - 2].staticEval != NO_EVAL && ss[ply].staticEval > ss[ply - 2].staticEval;
    }

    if (!PV && !inCheck) {
        if (depth <= 7 && eval - 80 * (depth - (int)improving) >= beta && std::abs(beta) < MATE_IN_MAX && eval < MATE_IN_MAX)
            return eval;
        if (depth <= 3 && eval + 200 + 100 * depth <= alpha && std::abs(alpha) < MATE_IN_MAX) {
            int v = qsearch<false>(alpha, alpha + 1, ply);
            if (stopped()) return 0;
            if (v <= alpha) return v;
        }
        if (depth >= 3 && eval >= beta && ss[ply - 1].move != NULL_MOVE && p.hasNonPawn(us) && beta > -MATE_IN_MAX) {
            int R = 3 + depth / 4 + std::min((eval - beta) / 200, 3);
            Position& np = pos[ply + 1];
            np = p;
            np.makeNull();
            keys[base + ply + 1] = np.key;
            ss[ply].move = NULL_MOVE;
            ss[ply].pt = 768;
            int v = -search<false>(-beta, -beta + 1, depth - R, ply + 1);
            if (stopped()) return 0;
            if (v >= beta) return v >= MATE_IN_MAX ? beta : v;
        }
    }
    if (depth >= 4 && !ttMove) depth--;  // internal iterative reduction

    Move mv[256], quiets[64];
    int sc[256];
    int n = generate<false>(p, mv);
    scoreMoves(p, mv, sc, n, ttMove, ply);

    int best = -INF, moveCount = 0, nq = 0;
    Move bestMove = NO_MOVE;
    const int origAlpha = alpha;

    for (int i = 0; i < n; i++) {
        int bi = i;
        for (int j = i + 1; j < n; j++) if (sc[j] > sc[bi]) bi = j;
        std::swap(mv[i], mv[bi]); std::swap(sc[i], sc[bi]);
        Move m = mv[i];
        if (root && !g_lim.searchmoves.empty() &&
            std::find(g_lim.searchmoves.begin(), g_lim.searchmoves.end(), m) == g_lim.searchmoves.end())
            continue;

        const bool cap = isCapture(m), promo = isPromo(m), quiet = !cap && !promo;
        Position& np = pos[ply + 1];
        np = p;
        np.make(m);
        if (np.leftInCheck()) continue;
        moveCount++;
        const bool givesCheck = np.inCheck();
        const int piece = p.board[moveFrom(m)];

        int qs = quiet ? quietScore(us, m, piece, ply) : 0;
        if (!root && best > -MATE_IN_MAX && p.hasNonPawn(us)) {
            if (quiet && !inCheck && !givesCheck) {
                if (depth <= 8 && moveCount > (improving ? 4 + depth * depth : 2 + depth * depth / 2)) continue; 
                if (depth <= 6 && eval + 90 + 80 * depth <= alpha) continue;                                      
                if (depth <= 4 && qs < -3000 * depth) continue;                                                    
                if (depth <= 6 && !p.seeGE(m, -30 * depth * depth)) continue;
            } else if (cap && !inCheck && depth <= 6 && !p.seeGE(m, -90 * depth)) {
                continue;
            }
        }

        int newDepth = depth - 1;
        if (givesCheck && p.seeGE(m, 0)) newDepth++; 

        keys[base + ply + 1] = np.key;
        ss[ply].move = m;
        ss[ply].pt = piece * 64 + moveTo(m);

        int score;
        if (moveCount == 1) {
            score = -search<PV>(-beta, -alpha, newDepth, ply + 1);
        } else {
            int r = 0;
            if (quiet && depth >= 3 && moveCount >= (PV ? 4 : 3)) {
                r = LMRTable[std::min(depth, 63)][std::min(moveCount, 63)];
                if (PV) r--;
                if (!improving) r++;
                if (givesCheck) r--;
                if (inCheck) r--;
                if (m == killers[ply][0] || m == killers[ply][1]) r--;
                r -= std::max(-2, std::min(2, qs / 6000));
                r = std::max(0, std::min(r, newDepth - 1));
            }
            int rd = newDepth - r;
            score = -search<false>(-alpha - 1, -alpha, rd, ply + 1);
            if (score > alpha && rd < newDepth) score = -search<false>(-alpha - 1, -alpha, newDepth, ply + 1);
            if (PV && score > alpha && score < beta) score = -search<true>(-beta, -alpha, newDepth, ply + 1);
        }
        if (stopped()) return 0;

        if (score > best) {
            best = score;
            if (score > alpha) {
                bestMove = m;
                alpha = score;
                if (PV) {
                    pv[ply][ply] = m;
                    for (int j = ply + 1; j < pvLen[ply + 1]; j++) pv[ply][j] = pv[ply + 1][j];
                    pvLen[ply] = std::max(pvLen[ply + 1], ply + 1);
                }
                if (alpha >= beta) {
                    if (quiet) updateQuietStats(p, ply, m, quiets, nq, depth);
                    break;
                }
            }
        }
        if (quiet && m != bestMove && nq < 64) quiets[nq++] = m;
    }

    if (moveCount == 0) return inCheck ? -MATE + ply : 0;
    int bound = best >= beta ? BOUND_LOWER : ((PV && bestMove) ? BOUND_EXACT : BOUND_UPPER);
    (void)origAlpha;
    TT.store(p.key, bestMove, best, inCheck ? NO_EVAL : ss[ply].staticEval, depth, bound, ply);
    return best;
}

static std::string scoreStr(int s) {
    if (std::abs(s) >= MATE_IN_MAX) {
        int n = (MATE - std::abs(s) + 1) / 2;
        return "mate " + std::to_string(s > 0 ? n : -n);
    }
    return "cp " + std::to_string(s);
}

static std::vector<std::unique_ptr<Searcher>> g_searchers;

static uint64_t totalNodes() {
    uint64_t t = 0;
    for (auto& s : g_searchers) t += (s->id == 0) ? s->nodes : s->nodesShared.load(std::memory_order_relaxed);
    return t;
}

static void printInfo(Searcher& s, int depth, int score, const char* bound) {
    int64_t el = std::max<int64_t>(nowMs() - g_start.load(), 0);
    uint64_t nodes = totalNodes();
    std::string line = "info depth " + std::to_string(depth) + " seldepth " + std::to_string(s.seldepth) + " multipv 1 score " + scoreStr(score) +
                       bound + " nodes " + std::to_string(nodes) + " nps " + std::to_string(el > 0 ? nodes * 1000 / el : nodes) +
                       " hashfull " + std::to_string(TT.hashfull()) + " time " + std::to_string(el) + " pv";
    for (int i = 0; i < s.pvLen[0]; i++) line += " " + moveStr(s.pv[0][i]);
    out(line);
}

void Searcher::iterate() {
    static const int skipSize[20] = {1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4};
    static const int skipPhase[20] = {0, 1, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, 6, 7};
    Move rm[256];
    int rn = generate<false>(pos[0], rm), legal = 0;
    Move firstLegal = NO_MOVE;
    for (int i = 0; i < rn; i++) {
        Position np = pos[0];
        np.make(rm[i]);
        if (!np.leftInCheck()) { if (!legal) firstLegal = rm[i]; legal++; }
    }
    bestMove = firstLegal;
    if (!legal) return;

    int maxD = g_lim.depth > 0 ? std::min(g_lim.depth, MAX_PLY - 1) : MAX_PLY - 1;
    int prevScore = 0, stable = 0;
    Move prevBest = NO_MOVE;
    for (int depth = 1; depth <= maxD; depth++) {
        if (id > 0) {
            int i = (id - 1) % 20;
            if (((depth + skipPhase[i]) / skipSize[i]) % 2) continue;
        }
        seldepth = 0;
        int delta = 14, alpha = -INF, beta = INF, sc = 0;
        if (depth >= 5) { alpha = std::max(prevScore - delta, -INF); beta = std::min(prevScore + delta, INF); }
        while (true) {
            sc = search<true>(alpha, beta, depth, 0);
            if (stopped()) break;
            if (sc <= alpha) {
                beta = (alpha + beta) / 2;
                alpha = std::max(sc - delta, -INF);
                if (id == 0 && pvLen[0] > 0 && depth > 8) printInfo(*this, depth, sc, " upperbound");
            } else if (sc >= beta) {
                beta = std::min(sc + delta, INF);
                if (id == 0 && pvLen[0] > 0 && depth > 8) printInfo(*this, depth, sc, " lowerbound");
            } else break;
            delta += delta / 2 + 5;
            if (delta > 500) { alpha = -INF; beta = INF; }
        }
        if (stopped()) break;
        bestScore = sc;
        if (pvLen[0] > 0) {
            bestMove = pv[0][0];
            ponderMove = pvLen[0] > 1 ? pv[0][1] : NO_MOVE;
        }
        completedDepth = depth;
        if (id != 0) { prevScore = sc; continue; }

        printInfo(*this, depth, sc, "");
        if (bestMove == prevBest) stable++; else stable = 0;
        double scale = stable >= 3 ? 0.7 : (stable == 0 && depth > 6 ? 1.3 : 1.0);
        if (sc < prevScore - 25) scale *= 1.25;
        if (g_lim.movetime > 0) scale = 1.0; 
        prevScore = sc;
        prevBest = bestMove;
        if (!g_pondering.load() && !g_lim.infinite && g_lim.timed) {
            int64_t el = nowMs() - g_start.load();
            if ((double)el > (double)g_optimum * scale) break;
            if (legal == 1 && depth >= 4) break;
        }
        if (!g_lim.infinite && !g_pondering.load() && sc >= MATE_IN_MAX && (MATE - sc) * 2 <= depth && g_lim.depth == 0) break;
    }
}

static Position g_pos;
static std::vector<U64> g_keys;
static std::thread g_thread;

static void runSearch(Position root, std::vector<U64> keys) {
    int nt = g_threads;
    while ((int)g_searchers.size() < nt) { g_searchers.emplace_back(new Searcher()); }
    while ((int)g_searchers.size() > nt) g_searchers.pop_back();
    for (int i = 0; i < nt; i++) { g_searchers[i]->id = i; g_searchers[i]->setup(root, keys); }
    TT.newSearch();
    std::vector<std::thread> helpers;
    for (int i = 1; i < nt; i++) helpers.emplace_back([i] { g_searchers[i]->iterate(); });
    Searcher& main = *g_searchers[0];
    main.iterate();
    while (!g_stop.load() && (g_pondering.load() || g_lim.infinite))
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    g_stop = true;
    for (auto& t : helpers) t.join();
    std::string res = "bestmove " + moveStr(main.bestMove);
    if (main.bestMove && main.ponderMove) res += " ponder " + moveStr(main.ponderMove);
    out(res);
}

static void stopSearch() {
    g_stop = true;
    g_pondering = false;
    if (g_thread.joinable()) g_thread.join();
}

static void startSearch() {
    stopSearch();
    g_stop = false;
    g_pondering = g_lim.ponder;
    g_start = nowMs();
    int us = g_pos.stm;
    g_lim.timed = false;
    if (!g_lim.infinite && !g_lim.ponder && g_lim.movetime > 0) {
        g_lim.timed = true;
        g_optimum = g_maxTime = std::max<int64_t>(g_lim.movetime - g_moveOverhead, 1);
    } else if (g_lim.time[us] > 0 || g_lim.ponder) {
        if (g_lim.time[us] > 0) {
            g_lim.timed = true;
            double t = (double)g_lim.time[us], inc = (double)g_lim.inc[us], ov = g_moveOverhead;
            int mtg = g_lim.movestogo > 0 ? std::min(g_lim.movestogo, 50) : 28;
            double opt = t / mtg + inc * 0.8;
            opt = std::min(opt, 0.8 * t - ov);
            double mx = std::min(0.9 * t - ov, opt * 3.5);
            opt = std::max(opt, 1.0);
            mx = std::max(mx, opt);
            g_optimum = (int64_t)opt;
            g_maxTime = (int64_t)mx;
        }
    } else if (g_lim.movetime > 0) {
        g_lim.timed = true;
        g_optimum = g_maxTime = std::max<int64_t>(g_lim.movetime - g_moveOverhead, 1);
    }
    g_thread = std::thread(runSearch, g_pos, g_keys);
}

struct PerftCase { const char* fen; int depth; U64 nodes; };

static bool runSelfTest() {
    static const PerftCase cases[] = {
        {"rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 5, 4865609ULL},
        {"r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1", 4, 4085603ULL},
        {"8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 5, 674624ULL},
        {"r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 4, 422333ULL},
        {"r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1", 4, 422333ULL},
        {"rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 4, 2103487ULL},
        {"r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", 4, 3894594ULL},
        {"8/8/8/8/k2Pp2Q/8/8/3K4 b - d3 0 1", 5, 117741ULL},
    };
    bool ok = true;
    for (const auto& c : cases) {
        Position p;
        if (!p.setFen(c.fen)) { out(std::string("FEN error: ") + c.fen); ok = false; continue; }
        int64_t t0 = nowMs();
        U64 n = perft(p, c.depth);
        int64_t dt = std::max<int64_t>(nowMs() - t0, 1);
        bool good = c.nodes == 0 || n == c.nodes;
        if (c.nodes == 0) out("perft " + std::to_string(c.depth) + " " + std::to_string(n) + " (no reference) " + c.fen);
        else out(std::string(good ? "PASS " : "FAIL ") + "depth " + std::to_string(c.depth) + " nodes " + std::to_string(n) + " expected " +
                 std::to_string(c.nodes) + " (" + std::to_string(n / dt) + " knps) " + c.fen);
        ok = ok && good;
    }
    {
        Position p;
        p.setFen("r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1");
        PRNG rng(12345);
        bool good = true;
        for (int g = 0; g < 200 && good; g++) {
            Position q = p;
            for (int ply = 0; ply < 120; ply++) {
                Move mv[256], legalM[256];
                int n = generate<false>(q, mv), l = 0;
                for (int i = 0; i < n; i++) { Position t = q; t.make(mv[i]); if (!t.leftInCheck()) legalM[l++] = mv[i]; }
                if (!l) break;
                q.make(legalM[rng.rand64() % l]);
                Position r;
                if (!r.setFen(q.fen())) { good = false; break; }
                if (r.key != q.key || r.pawnKey != q.pawnKey || r.mg != q.mg || r.eg != q.eg || r.phase != q.phase || q.computeKey() != q.key) {
                    out("incremental state mismatch at fen " + q.fen());
                    good = false;
                    break;
                }
            }
        }
        out(std::string(good ? "PASS" : "FAIL") + " incremental hash/eval consistency");
        ok = ok && good;
    }
    out(ok ? "selftest: ALL PASSED" : "selftest: FAILURES");
    return ok;
}

static void runBench(int depth) {
    static const char* fens[] = {
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
        "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1",
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
        "2rq1rk1/pp1bppbp/3p1np1/8/3NP3/2N1BP2/PPPQ2PP/2KR1B1R w - - 0 1",
        "8/5pk1/6p1/8/5P2/6K1/8/8 w - - 0 1"};
    g_lim = SearchLimits();
    g_lim.depth = depth;
    uint64_t total = 0;
    int64_t t0 = nowMs();
    for (const char* f : fens) {
        Position p;
        p.setFen(f);
        g_pos = p;
        g_keys.assign(1, p.key);
        TT.clear();
        g_stop = false; g_pondering = false;
        g_start = nowMs();
        std::vector<std::unique_ptr<Searcher>> keep;
        g_threads = 1;
        g_searchers.clear();
        g_searchers.emplace_back(new Searcher());
        g_searchers[0]->id = 0;
        g_searchers[0]->setup(p, g_keys);
        g_searchers[0]->iterate();
        total += g_searchers[0]->nodes;
        out(std::string("bench ") + f + " -> " + moveStr(g_searchers[0]->bestMove) + " nodes " + std::to_string(g_searchers[0]->nodes));
    }
    int64_t dt = std::max<int64_t>(nowMs() - t0, 1);
    out("bench total nodes " + std::to_string(total) + " time " + std::to_string(dt) + " ms nps " + std::to_string(total * 1000 / dt));
    g_searchers.clear();
}

static const char* START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

static void printBoard(const Position& p) {
    std::string s;
    for (int r = 7; r >= 0; r--) {
        s += std::to_string(r + 1) + "  ";
        for (int f = 0; f < 8; f++) {
            int pc = p.board[r * 8 + f];
            s += pc == NO_PIECE ? '.' : PIECE_CHARS[pc];
            s += ' ';
        }
        s += "\n";
    }
    s += "\n   a b c d e f g h\nFEN: " + p.fen() + "\nKey: " + std::to_string(p.key);
    out(s);
}

static std::string lower(std::string s) { for (auto& c : s) c = (char)std::tolower((unsigned char)c); return s; }

static void cmdPosition(std::istringstream& is) {
    std::string tok, fen;
    is >> tok;
    Position np;
    if (tok == "startpos") {
        np.setFen(START_FEN);
        is >> tok; 
    } else if (tok == "fen") {
        while (is >> tok && tok != "moves") fen += tok + " ";
        if (!np.setFen(fen)) { std::fprintf(stderr, "info string invalid FEN\n"); return; }
    } else return;
    std::vector<U64> keys{np.key};
    if (tok == "moves") {
        while (is >> tok) {
            Move m = parseMove(np, tok);
            if (!m) { std::fprintf(stderr, "info string illegal move %s\n", tok.c_str()); break; }
            np.make(m);
            keys.push_back(np.key);
        }
    }
    g_pos = np;
    g_keys = keys;
}

static void cmdGo(std::istringstream& is) {
    SearchLimits lim;
    std::string tok;
    bool doPerft = false;
    int perftDepth = 0;
    while (is >> tok) {
        if (tok == "wtime") is >> lim.time[WHITE];
        else if (tok == "btime") is >> lim.time[BLACK];
        else if (tok == "winc") is >> lim.inc[WHITE];
        else if (tok == "binc") is >> lim.inc[BLACK];
        else if (tok == "movestogo") is >> lim.movestogo;
        else if (tok == "depth") is >> lim.depth;
        else if (tok == "nodes") is >> lim.nodes;
        else if (tok == "movetime") is >> lim.movetime;
        else if (tok == "mate") { int d; is >> d; lim.depth = std::max(1, 2 * d); }
        else if (tok == "infinite") lim.infinite = true;
        else if (tok == "ponder") lim.ponder = true;
        else if (tok == "perft") { doPerft = true; is >> perftDepth; }
        else if (tok == "searchmoves") {
            std::streampos pos;
            while (true) {
                pos = is.tellg();
                if (!(is >> tok)) break;
                Move m = parseMove(g_pos, tok);
                if (!m) { is.clear(); is.seekg(pos); break; }
                lim.searchmoves.push_back(m);
            }
        }
    }
    if (doPerft) {
        Move mv[256];
        int n = generate<false>(g_pos, mv);
        U64 total = 0;
        int64_t t0 = nowMs();
        for (int i = 0; i < n; i++) {
            Position np = g_pos;
            np.make(mv[i]);
            if (np.leftInCheck()) continue;
            U64 c = perftDepth <= 1 ? 1 : perft(np, perftDepth - 1);
            total += c;
            out(moveStr(mv[i]) + ": " + std::to_string(c));
        }
        int64_t dt = std::max<int64_t>(nowMs() - t0, 1);
        out("\nNodes searched: " + std::to_string(total) + "  (" + std::to_string(total / dt) + " knps)");
        return;
    }
    if (!lim.infinite && !lim.ponder && !lim.depth && !lim.movetime && !lim.nodes && !lim.time[WHITE] && !lim.time[BLACK])
        lim.infinite = true;
    g_lim = lim;
    startSearch();
}

static void cmdSetOption(std::istringstream& is) {
    std::string tok, name, value;
    is >> tok; 
    while (is >> tok && tok != "value") name += (name.empty() ? "" : " ") + tok;
    while (is >> tok) value += (value.empty() ? "" : " ") + tok;
    name = lower(name);
    if (name == "hash") {
        stopSearch();
        int mb = std::max(1, std::min(65536, std::atoi(value.c_str())));
        TT.resize((size_t)mb);
    } else if (name == "threads") {
        stopSearch();
        g_threads = std::max(1, std::min(256, std::atoi(value.c_str())));
    } else if (name == "clear hash") {
        stopSearch();
        TT.clear();
    } else if (name == "ponder") {
        g_ponderOpt = lower(value) == "true";
    } else if (name == "move overhead") {
        g_moveOverhead = std::max(0, std::min(5000, std::atoi(value.c_str())));
    }
}

static void uciLoop() {
    g_pos.setFen(START_FEN);
    g_keys.assign(1, g_pos.key);
    std::string line;
    while (std::getline(std::cin, line)) {
        std::istringstream is(line);
        std::string cmd;
        if (!(is >> cmd)) continue;
        if (cmd == "uci") {
            out("id name Hunyadi 4.0\nid author ThatHungarian\n"
                "option name Hash type spin default 64 min 1 max 65536\n"
                "option name Threads type spin default 1 min 1 max 256\n"
                "option name Clear Hash type button\n"
                "option name Ponder type check default false\n"
                "option name Move Overhead type spin default 20 min 0 max 5000\n"
                "uciok");
        } else if (cmd == "isready") out("readyok");
        else if (cmd == "ucinewgame") {
            stopSearch();
            TT.clear();
            g_searchers.clear();
            g_pos.setFen(START_FEN);
            g_keys.assign(1, g_pos.key);
        } else if (cmd == "position") { stopSearch(); cmdPosition(is); }
        else if (cmd == "go") cmdGo(is);
        else if (cmd == "stop") stopSearch();
        else if (cmd == "ponderhit") { g_start = nowMs(); g_pondering = false; }
        else if (cmd == "setoption") cmdSetOption(is);
        else if (cmd == "quit") break;
        else if (cmd == "d") printBoard(g_pos);
        else if (cmd == "eval") {
            Searcher s;
            out("static eval (side to move): " + std::to_string(s.evaluate(g_pos)));
        } else if (cmd == "perft") {
            int d = 1; is >> d;
            std::istringstream gs("perft " + std::to_string(d));
            cmdGo(gs);
        } else if (cmd == "selftest") runSelfTest();
        else if (cmd == "bench") { int d = 10; is >> d; stopSearch(); runBench(d); }
    }
    stopSearch();
}

int main(int argc, char** argv) {
    initTables();
    TT.resize(64);
    if (argc > 1) {
        std::string a = argv[1];
        if (a == "selftest") return runSelfTest() ? 0 : 1;
        if (a == "bench") { runBench(argc > 2 ? std::atoi(argv[2]) : 10); return 0; }
    }
    uciLoop();
    return 0;
}
