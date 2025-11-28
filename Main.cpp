#include <iostream>
#include <string>
#include <vector>
#include <array>
#include <optional>
#include <chrono>
#include <fstream>
#include <filesystem>
#include <random>
#include <sstream>
#include <cstdint>
#include <algorithm>
#include <cstring>
#include <cctype>
#include <climits>
#include <atomic>

namespace fs = std::filesystem;

// Constants & Types
enum class Color { WHITE = 0, BLACK = 1, NONE = 2 };
enum class PieceType { PAWN = 0, KNIGHT = 1, BISHOP = 2, ROOK = 3, QUEEN = 4, KING = 5, NONE = 6 };
enum class Square : uint8_t {
    A1, B1, C1, D1, E1, F1, G1, H1,
    A2, B2, C2, D2, E2, F2, G2, H2,
    A3, B3, C3, D3, E3, F3, G3, H3,
    A4, B4, C4, D4, E4, F4, G4, H4,
    A5, B5, C5, D5, E5, F5, G5, H5,
    A6, B6, C6, D6, E6, F6, G6, H6,
    A7, B7, C7, D7, E7, F7, G7, H7,
    A8, B8, C8, D8, E8, F8, G8, H8, NONE = 255
};

constexpr int SQUARE_COUNT = 64;
constexpr int MAX_PLY = 128;

struct Piece {
    PieceType type;
    Color color;
};

struct Move {
    Square from;
    Square to;
    PieceType promotion;
    int score = 0;
    
    Move(Square f = Square::NONE, Square t = Square::NONE, PieceType p = PieceType::NONE)
        : from(f), to(t), promotion(p) {}
    
    bool operator==(const Move& other) const {
        return from == other.from && to == other.to && promotion == other.promotion;
    }
    
    bool operator!=(const Move& other) const {
        return !(*this == other);
    }
    
    std::string toUci() const {
        static const char* files = "abcdefgh";
        static const char* ranks = "12345678";
        if (from == Square::NONE || to == Square::NONE) return "0000";
        std::string uci;
        uci += files[static_cast<int>(from) % 8];
        uci += ranks[static_cast<int>(from) / 8];
        uci += files[static_cast<int>(to) % 8];
        uci += ranks[static_cast<int>(to) / 8];
        if (promotion != PieceType::NONE) {
            static const char* promos = " nbrq";
            uci += promos[static_cast<int>(promotion)];
        }
        return uci;
    }
    
    struct Hash {
        size_t operator()(const Move& m) const {
            return static_cast<size_t>(static_cast<int>(m.from) * 64 + static_cast<int>(m.to));
        }
    };
};

inline int popcount(uint64_t x) { return __builtin_popcountll(x); }
inline int lsbIndex(uint64_t x) { return __builtin_ctzll(x); }

// Board State
struct BoardState {
    uint64_t pieces[2][6];
    uint64_t occupied;
    uint64_t empty;
    Color sideToMove;
    Square enPassant;
    bool castlingRights[2][2];
    int halfmoveClock;
    int fullmoveNumber;
};

// Attack Tables
namespace Attacks {
    const std::array<int, 8> KNIGHT_DELTAS = {-17, -15, -10, -6, 6, 10, 15, 17};
    const std::array<int, 8> KING_DELTAS = {-9, -8, -7, -1, 1, 7, 8, 9};
    
    inline uint64_t pawnAttacks(Color color, uint64_t pawns) {
        if (color == Color::WHITE) {
            return ((pawns << 7) & ~0x0101010101010101ULL) | ((pawns << 9) & ~0x8080808080808080ULL);
        } else {
            return ((pawns >> 7) & ~0x8080808080808080ULL) | ((pawns >> 9) & ~0x0101010101010101ULL);
        }
    }
    
    inline uint64_t knightAttacks(Square sq) {
        int s = static_cast<int>(sq);
        uint64_t bb = 0;
        if (s % 8 > 0 && s / 8 > 1) bb |= (1ULL << (s - 17));
        if (s % 8 < 7 && s / 8 > 1) bb |= (1ULL << (s - 15));
        if (s % 8 > 1 && s / 8 > 0) bb |= (1ULL << (s - 10));
        if (s % 8 < 6 && s / 8 > 0) bb |= (1ULL << (s - 6));
        if (s % 8 > 1 && s / 8 < 7) bb |= (1ULL << (s + 6));
        if (s % 8 < 6 && s / 8 < 7) bb |= (1ULL << (s + 10));
        if (s % 8 > 0 && s / 8 < 6) bb |= (1ULL << (s + 15));
        if (s % 8 < 7 && s / 8 < 6) bb |= (1ULL << (s + 17));
        return bb;
    }
    
    inline uint64_t kingAttacks(Square sq) {
        int s = static_cast<int>(sq);
        uint64_t bb = 0;
        if (s % 8 > 0 && s / 8 > 0) bb |= (1ULL << (s - 9));
        if (s / 8 > 0) bb |= (1ULL << (s - 8));
        if (s % 8 < 7 && s / 8 > 0) bb |= (1ULL << (s - 7));
        if (s % 8 > 0) bb |= (1ULL << (s - 1));
        if (s % 8 < 7) bb |= (1ULL << (s + 1));
        if (s % 8 > 0 && s / 8 < 7) bb |= (1ULL << (s + 7));
        if (s / 8 < 7) bb |= (1ULL << (s + 8));
        if (s % 8 < 7 && s / 8 < 7) bb |= (1ULL << (s + 9));
        return bb;
    }
    
    inline uint64_t rookAttacks(Square sq, uint64_t occupied) {
        int s = static_cast<int>(sq);
        uint64_t attacks = 0;
        int r = s / 8, f = s % 8;
        
        for (int i = 1; i < 8; ++i) {
            if (f + i >= 8) break;
            attacks |= (1ULL << (s + i));
            if (occupied & (1ULL << (s + i))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (f - i < 0) break;
            attacks |= (1ULL << (s - i));
            if (occupied & (1ULL << (s - i))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (r + i >= 8) break;
            attacks |= (1ULL << (s + i * 8));
            if (occupied & (1ULL << (s + i * 8))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (r - i < 0) break;
            attacks |= (1ULL << (s - i * 8));
            if (occupied & (1ULL << (s - i * 8))) break;
        }
        return attacks;
    }
    
    inline uint64_t bishopAttacks(Square sq, uint64_t occupied) {
        int s = static_cast<int>(sq);
        uint64_t attacks = 0;
        int r = s / 8, f = s % 8;
        
        for (int i = 1; i < 8; ++i) {
            if (f + i >= 8 || r + i >= 8) break;
            attacks |= (1ULL << (s + i * 9));
            if (occupied & (1ULL << (s + i * 9))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (f - i < 0 || r + i >= 8) break;
            attacks |= (1ULL << (s + i * 7));
            if (occupied & (1ULL << (s + i * 7))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (f + i >= 8 || r - i < 0) break;
            attacks |= (1ULL << (s - i * 7));
            if (occupied & (1ULL << (s - i * 7))) break;
        }
        for (int i = 1; i < 8; ++i) {
            if (f - i < 0 || r - i < 0) break;
            attacks |= (1ULL << (s - i * 9));
            if (occupied & (1ULL << (s - i * 9))) break;
        }
        return attacks;
    }
    
    inline uint64_t queenAttacks(Square sq, uint64_t occupied) {
        return rookAttacks(sq, occupied) | bishopAttacks(sq, occupied);
    }
}

// Board Class
class Board {
private:
    std::array<uint64_t, 6> pieces_[2];
    uint64_t occupied_ = 0;
    uint64_t empty_ = ~0ULL;
    Color sideToMove_ = Color::WHITE;
    Square enPassant_ = Square::NONE;
    bool castlingRights_[2][2] = {{true, true}, {true, true}};
    int halfmoveClock_ = 0;
    int fullmoveNumber_ = 1;
    std::vector<Move> moveStack_;
    std::vector<BoardState> stateStack_;
    
    inline void updateBitboards() {
        occupied_ = 0;
        for (int c = 0; c < 2; ++c) {
            for (int p = 0; p < 6; ++p) occupied_ |= pieces_[c][p];
        }
        empty_ = ~occupied_;
    }
    
    inline bool isSquareAttacked(Square sq, Color attacker) const {
        uint64_t occ = occupied_;
        int s = static_cast<int>(sq);
        
        if (Attacks::pawnAttacks(attacker, pieces_[static_cast<int>(attacker)][0]) & (1ULL << s)) return true;
        
        uint64_t knights = pieces_[static_cast<int>(attacker)][1];
        while (knights) {
            int ksq = lsbIndex(knights);
            if (Attacks::knightAttacks(static_cast<Square>(ksq)) & (1ULL << s)) return true;
            knights &= knights - 1;
        }
        
        uint64_t bishops = pieces_[static_cast<int>(attacker)][2];
        while (bishops) {
            int bsq = lsbIndex(bishops);
            if (Attacks::bishopAttacks(static_cast<Square>(bsq), occ) & (1ULL << s)) return true;
            bishops &= bishops - 1;
        }
        
        uint64_t rooks = pieces_[static_cast<int>(attacker)][3];
        while (rooks) {
            int rsq = lsbIndex(rooks);
            if (Attacks::rookAttacks(static_cast<Square>(rsq), occ) & (1ULL << s)) return true;
            rooks &= rooks - 1;
        }
        
        uint64_t queens = pieces_[static_cast<int>(attacker)][4];
        while (queens) {
            int qsq = lsbIndex(queens);
            if (Attacks::queenAttacks(static_cast<Square>(qsq), occ) & (1ULL << s)) return true;
            queens &= queens - 1;
        }
        
        int ksq = __builtin_ctzll(pieces_[static_cast<int>(attacker)][5]);
        if (Attacks::kingAttacks(static_cast<Square>(ksq)) & (1ULL << s)) return true;
        
        return false;
    }

public:
    Board() {
        for (int c = 0; c < 2; ++c) {
            for (int p = 0; p < 6; ++p) pieces_[c][p] = 0;
            castlingRights_[c][0] = true;
            castlingRights_[c][1] = true;
        }
        reset();
    }
    
    void reset() {
        pieces_[0][0] = 0x000000000000FF00ULL;  
        pieces_[0][1] = 0x0000000000000042ULL;  
        pieces_[0][2] = 0x0000000000000024ULL;  
        pieces_[0][3] = 0x0000000000000081ULL;  
        pieces_[0][4] = 0x0000000000000008ULL;  
        pieces_[0][5] = 0x0000000000000010ULL;  
        pieces_[1][0] = 0x00FF000000000000ULL;  
        pieces_[1][1] = 0x4200000000000000ULL;  
        pieces_[1][2] = 0x2400000000000000ULL;  
        pieces_[1][3] = 0x8100000000000000ULL;  
        pieces_[1][4] = 0x0800000000000000ULL;  
        pieces_[1][5] = 0x1000000000000000ULL;  
        updateBitboards();
        sideToMove_ = Color::WHITE;
        enPassant_ = Square::NONE;
        castlingRights_[0][0] = castlingRights_[0][1] = true;
        castlingRights_[1][0] = castlingRights_[1][1] = true;
        halfmoveClock_ = 0;
        fullmoveNumber_ = 1;
        moveStack_.clear();
        stateStack_.clear();
    }
    
    void setFen(const std::string& fen) {
        reset();
        std::istringstream iss(fen);
        std::string boardPart, colorPart, castlingPart, epPart;
        iss >> boardPart >> colorPart >> castlingPart >> epPart;
        
        int sq = 56;
        for (char ch : boardPart) {
            if (ch == '/') sq -= 16;
            else if (isdigit(ch)) sq += (ch - '0');
            else {
                Color col = isupper(ch) ? Color::WHITE : Color::BLACK;
                PieceType pt = PieceType::NONE;
                switch (tolower(ch)) {
                    case 'p': pt = PieceType::PAWN; break;
                    case 'n': pt = PieceType::KNIGHT; break;
                    case 'b': pt = PieceType::BISHOP; break;
                    case 'r': pt = PieceType::ROOK; break;
                    case 'q': pt = PieceType::QUEEN; break;
                    case 'k': pt = PieceType::KING; break;
                }
                if (pt != PieceType::NONE) {
                    pieces_[static_cast<int>(col)][static_cast<int>(pt)] |= (1ULL << sq);
                }
                ++sq;
            }
        }
        
        updateBitboards();
        sideToMove_ = (colorPart == "w") ? Color::WHITE : Color::BLACK;
        
        castlingRights_[0][0] = castlingRights_[0][1] = false;
        castlingRights_[1][0] = castlingRights_[1][1] = false;
        for (char ch : castlingPart) {
            if (ch == 'K') castlingRights_[0][0] = true;
            else if (ch == 'Q') castlingRights_[0][1] = true;
            else if (ch == 'k') castlingRights_[1][0] = true;
            else if (ch == 'q') castlingRights_[1][1] = true;
        }
        
        if (epPart != "-") {
            int file = epPart[0] - 'a';
            int rank = epPart[1] - '1';
            enPassant_ = static_cast<Square>(rank * 8 + file);
        }
        
        iss >> halfmoveClock_ >> fullmoveNumber_;
    }
    
    Color turn() const { return sideToMove_; }
    Square enPassant() const { return enPassant_; }
    uint64_t occupied() const { return occupied_; }
    
    uint64_t getBitboard(PieceType type, Color color) const {
        return pieces_[static_cast<int>(color)][static_cast<int>(type)];
    }
    
    uint64_t computeHash() const {
        uint64_t hash = 0x9e3779b97f4a7c15ULL;
        for (int c = 0; c < 2; ++c) {
            for (int p = 0; p < 6; ++p) {
                uint64_t bb = pieces_[c][p];
                while (bb) {
                    int sq = lsbIndex(bb);
                    hash ^= (c * 6ULL + p + 1) * 0x123456789abcdef0ULL ^ (sq * 0xbf58476d1ce4e5b9ULL);
                    bb &= bb - 1;
                }
            }
        }
        hash ^= static_cast<uint64_t>(sideToMove_) * 0xabcdef0123456789ULL;
        return hash;
    }
    
    Piece pieceAt(Square sq) const {
        if (sq == Square::NONE) return {PieceType::NONE, Color::NONE};
        uint64_t mask = 1ULL << static_cast<int>(sq);
        for (int c = 0; c < 2; ++c) {
            for (int p = 0; p < 6; ++p) {
                if (pieces_[c][p] & mask) {
                    return {static_cast<PieceType>(p), static_cast<Color>(c)};
                }
            }
        }
        return {PieceType::NONE, Color::NONE};
    }
    
    bool isCapture(const Move& move) const {
        return pieceAt(move.to).type != PieceType::NONE;
    }
    
    bool isCheckmate() const {
        return isInCheck(sideToMove_) && generateMoves().empty();
    }
    
    bool isStalemate() const {
        return !isInCheck(sideToMove_) && generateMoves().empty();
    }
    
    bool isInsufficientMaterial() const {
        // K vs K
        if (__builtin_popcountll(occupied_) == 2) return true;
        
        uint64_t whitePieces = pieces_[0][0] | pieces_[0][1] | pieces_[0][2] | pieces_[0][3] | pieces_[0][4];
        uint64_t blackPieces = pieces_[1][0] | pieces_[1][1] | pieces_[1][2] | pieces_[1][3] | pieces_[1][4];
        
        if (whitePieces == 0 && __builtin_popcountll(blackPieces) == 1) return true;
        if (blackPieces == 0 && __builtin_popcountll(whitePieces) == 1) return true;
        
        if (whitePieces == 0 && blackPieces == 0) {
            uint64_t whiteBishops = pieces_[0][2];
            uint64_t blackBishops = pieces_[1][2];
            if (__builtin_popcountll(whiteBishops) == 1 && __builtin_popcountll(blackBishops) == 1) {
                int whiteSq = lsbIndex(whiteBishops);
                int blackSq = lsbIndex(blackBishops);
                bool whiteDark = ((whiteSq / 8 + whiteSq % 8) % 2) == 0;
                bool blackDark = ((blackSq / 8 + blackSq % 8) % 2) == 0;
                return whiteDark == blackDark;
            }
        }
        
        return false;
    }
    
    bool isGameOver() const {
        return isCheckmate() || isStalemate() || isInsufficientMaterial();
    }
    
    void makeMove(const Move& move) {
        BoardState state;
        memcpy(state.pieces, pieces_, sizeof(pieces_));
        state.occupied = occupied_;
        state.empty = empty_;
        state.sideToMove = sideToMove_;
        state.enPassant = enPassant_;
        memcpy(state.castlingRights, castlingRights_, sizeof(castlingRights_));
        state.halfmoveClock = halfmoveClock_;
        state.fullmoveNumber = fullmoveNumber_;
        stateStack_.push_back(state);
        
        int from = static_cast<int>(move.from);
        int to = static_cast<int>(move.to);
        Color us = sideToMove_;
        Color them = (us == Color::WHITE) ? Color::BLACK : Color::WHITE;
        
        Piece moved = pieceAt(move.from);
        Piece captured = pieceAt(move.to);
        
        uint64_t fromMask = 1ULL << from;
        uint64_t toMask = 1ULL << to;
        pieces_[static_cast<int>(us)][static_cast<int>(moved.type)] &= ~fromMask;
        pieces_[static_cast<int>(us)][static_cast<int>(moved.type)] |= toMask;
        
        if (captured.type != PieceType::NONE) {
            pieces_[static_cast<int>(them)][static_cast<int>(captured.type)] &= ~toMask;
        }
        
        if (moved.type == PieceType::PAWN) {
            if (std::abs(to - from) == 16) {
                enPassant_ = static_cast<Square>((from + to) / 2);
            }
            
            if (move.to == enPassant_) {
                int epPawn = (us == Color::WHITE) ? to - 8 : to + 8;
                pieces_[static_cast<int>(them)][0] &= ~(1ULL << epPawn);
            }
            
            if (move.promotion != PieceType::NONE) {
                pieces_[static_cast<int>(us)][0] &= ~toMask;
                pieces_[static_cast<int>(us)][static_cast<int>(move.promotion)] |= toMask;
            }
        }
        
        if (moved.type == PieceType::KING) {
            castlingRights_[static_cast<int>(us)][0] = false;
            castlingRights_[static_cast<int>(us)][1] = false;
            
            if (std::abs(to - from) == 2 && from % 8 == 4) {
                bool kingSide = to > from;
                int rookFrom = kingSide ? from + 3 : from - 4;
                int rookTo = kingSide ? from + 1 : from - 1;
                
                uint64_t rookToMask = 1ULL << rookTo;
                for (int c = 0; c < 2; ++c) {
                    for (int p = 0; p < 6; ++p) {
                        pieces_[c][p] &= ~rookToMask;
                    }
                }
                
                pieces_[static_cast<int>(us)][3] &= ~(1ULL << rookFrom);
                pieces_[static_cast<int>(us)][3] |= rookToMask;
            }
        }
        
        if (moved.type == PieceType::ROOK) {
            if (from == 0 || from == 56) castlingRights_[static_cast<int>(us)][1] = false;
            if (from == 7 || from == 63) castlingRights_[static_cast<int>(us)][0] = false;
        }
        
        if (moved.type != PieceType::PAWN || std::abs(to - from) != 16) {
            enPassant_ = Square::NONE;
        }
        
        updateBitboards();
        sideToMove_ = them;
        moveStack_.push_back(move);
        
        if (moved.type == PieceType::PAWN || captured.type != PieceType::NONE) {
            halfmoveClock_ = 0;
        } else {
            ++halfmoveClock_;
        }
        
        if (us == Color::BLACK) ++fullmoveNumber_;
    }
    
    void unmakeMove() {
        if (!stateStack_.empty() && !moveStack_.empty()) {
            BoardState state = stateStack_.back();
            stateStack_.pop_back();
            
            memcpy(pieces_, state.pieces, sizeof(pieces_));
            occupied_ = state.occupied;
            empty_ = state.empty;
            sideToMove_ = state.sideToMove;
            enPassant_ = state.enPassant;
            memcpy(castlingRights_, state.castlingRights, sizeof(castlingRights_));
            halfmoveClock_ = state.halfmoveClock;
            fullmoveNumber_ = state.fullmoveNumber;
            
            moveStack_.pop_back();
        }
    }
    
    void makeNullMove() {
        BoardState state;
        memcpy(state.pieces, pieces_, sizeof(pieces_));
        state.occupied = occupied_;
        state.empty = empty_;
        state.sideToMove = sideToMove_;
        state.enPassant = enPassant_;
        memcpy(state.castlingRights, castlingRights_, sizeof(castlingRights_));
        state.halfmoveClock = halfmoveClock_;
        state.fullmoveNumber = fullmoveNumber_;
        stateStack_.push_back(state);
        
        enPassant_ = Square::NONE;
        sideToMove_ = (sideToMove_ == Color::WHITE) ? Color::BLACK : Color::WHITE;
        halfmoveClock_++;
    }
    
    void unmakeNullMove() {
        if (!stateStack_.empty()) {
            BoardState state = stateStack_.back();
            stateStack_.pop_back();
            
            memcpy(pieces_, state.pieces, sizeof(pieces_));
            occupied_ = state.occupied;
            empty_ = state.empty;
            sideToMove_ = state.sideToMove;
            enPassant_ = state.enPassant;
            memcpy(castlingRights_, state.castlingRights, sizeof(castlingRights_));
            halfmoveClock_ = state.halfmoveClock;
            fullmoveNumber_ = state.fullmoveNumber;
        }
    }
    
    std::vector<Move> generateMoves() const {
        std::vector<Move> moves;
        Color us = sideToMove_;
        Color them = (us == Color::WHITE) ? Color::BLACK : Color::WHITE;
        uint64_t occ = occupied_;
        uint64_t emptySq = empty_;
        uint64_t enemy = 0;
        for (int p = 0; p < 6; ++p) enemy |= pieces_[static_cast<int>(them)][p];
        
        uint64_t pawns = pieces_[static_cast<int>(us)][0];
        while (pawns) {
            int from = lsbIndex(pawns);
            pawns &= pawns - 1;
            
            if (us == Color::WHITE) {
                int to = from + 8;
                if (to < 64 && (emptySq & (1ULL << to))) {
                    if (to >= 56) {
                        for (int promo = 1; promo <= 4; ++promo) {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                             static_cast<PieceType>(promo));
                        }
                    } else {
                        moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        if (from >= 8 && from < 16) {
                            int to2 = from + 16;
                            if (emptySq & (1ULL << to2)) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to2));
                            }
                        }
                    }
                }
                if (from % 8 > 0) {
                    int to = from + 7;
                    if (to < 64 && (enemy & (1ULL << to) || static_cast<Square>(to) == enPassant_)) {
                        if (to >= 56) {
                            for (int promo = 1; promo <= 4; ++promo) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                                 static_cast<PieceType>(promo));
                            }
                        } else {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        }
                    }
                }
                if (from % 8 < 7) {
                    int to = from + 9;
                    if (to < 64 && (enemy & (1ULL << to) || static_cast<Square>(to) == enPassant_)) {
                        if (to >= 56) {
                            for (int promo = 1; promo <= 4; ++promo) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                                 static_cast<PieceType>(promo));
                            }
                        } else {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        }
                    }
                }
            } else {
                int to = from - 8;
                if (to >= 0 && (emptySq & (1ULL << to))) {
                    if (to <= 7) {
                        for (int promo = 1; promo <= 4; ++promo) {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                             static_cast<PieceType>(promo));
                        }
                    } else {
                        moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        if (from >= 48 && from < 56) {
                            int to2 = from - 16;
                            if (emptySq & (1ULL << to2)) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to2));
                            }
                        }
                    }
                }
                if (from % 8 > 0) {
                    int to = from - 9;
                    if (to >= 0 && (enemy & (1ULL << to) || static_cast<Square>(to) == enPassant_)) {
                        if (to <= 7) {
                            for (int promo = 1; promo <= 4; ++promo) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                                 static_cast<PieceType>(promo));
                            }
                        } else {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        }
                    }
                }
                if (from % 8 < 7) {
                    int to = from - 7;
                    if (to >= 0 && (enemy & (1ULL << to) || static_cast<Square>(to) == enPassant_)) {
                        if (to <= 7) {
                            for (int promo = 1; promo <= 4; ++promo) {
                                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to), 
                                                 static_cast<PieceType>(promo));
                            }
                        } else {
                            moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                        }
                    }
                }
            }
        }
        
        uint64_t knights = pieces_[static_cast<int>(us)][1];
        while (knights) {
            int from = lsbIndex(knights);
            knights &= knights - 1;
            uint64_t attacks = Attacks::knightAttacks(static_cast<Square>(from));
            attacks &= (emptySq | enemy);
            while (attacks) {
                int to = lsbIndex(attacks);
                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                attacks &= attacks - 1;
            }
        }
        
        uint64_t bishops = pieces_[static_cast<int>(us)][2];
        while (bishops) {
            int from = lsbIndex(bishops);
            bishops &= bishops - 1;
            uint64_t attacks = Attacks::bishopAttacks(static_cast<Square>(from), occ);
            attacks &= (emptySq | enemy);
            while (attacks) {
                int to = lsbIndex(attacks);
                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                attacks &= attacks - 1;
            }
        }
        
        uint64_t rooks = pieces_[static_cast<int>(us)][3];
        while (rooks) {
            int from = lsbIndex(rooks);
            rooks &= rooks - 1;
            uint64_t attacks = Attacks::rookAttacks(static_cast<Square>(from), occ);
            attacks &= (emptySq | enemy);
            while (attacks) {
                int to = lsbIndex(attacks);
                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                attacks &= attacks - 1;
            }
        }
        
        uint64_t queens = pieces_[static_cast<int>(us)][4];
        while (queens) {
            int from = lsbIndex(queens);
            queens &= queens - 1;
            uint64_t attacks = Attacks::queenAttacks(static_cast<Square>(from), occ);
            attacks &= (emptySq | enemy);
            while (attacks) {
                int to = lsbIndex(attacks);
                moves.emplace_back(static_cast<Square>(from), static_cast<Square>(to));
                attacks &= attacks - 1;
            }
        }
        
        int kingSq = __builtin_ctzll(pieces_[static_cast<int>(us)][5]);
        uint64_t attacks = Attacks::kingAttacks(static_cast<Square>(kingSq));
        attacks &= (emptySq | enemy);
        while (attacks) {
            int to = lsbIndex(attacks);
            moves.emplace_back(static_cast<Square>(kingSq), static_cast<Square>(to));
            attacks &= attacks - 1;
        }
        
        int backRank = (us == Color::WHITE) ? 0 : 7;
        
        if (castlingRights_[static_cast<int>(us)][0] && kingSq == backRank * 8 + 4 &&
            !(occ & (1ULL << (kingSq + 1))) && !(occ & (1ULL << (kingSq + 2))) &&
            !isSquareAttacked(static_cast<Square>(kingSq + 1), them) &&
            !isSquareAttacked(static_cast<Square>(kingSq + 2), them)) {
            moves.emplace_back(static_cast<Square>(kingSq), static_cast<Square>(kingSq + 2));
        }
        
        if (castlingRights_[static_cast<int>(us)][1] && kingSq == backRank * 8 + 4 &&
            !(occ & (1ULL << (kingSq - 1))) && !(occ & (1ULL << (kingSq - 2))) &&
            !(occ & (1ULL << (kingSq - 3))) &&
            !isSquareAttacked(static_cast<Square>(kingSq - 1), them) &&
            !isSquareAttacked(static_cast<Square>(kingSq - 2), them)) {
            moves.emplace_back(static_cast<Square>(kingSq), static_cast<Square>(kingSq - 2));
        }
        
        std::vector<Move> legalMoves;
        for (const auto& move : moves) {
            Board temp = *this;
            temp.makeMove(move);
            if (!temp.isInCheck(us)) legalMoves.push_back(move);
        }
        
        return legalMoves;
    }
    
    std::vector<Move> generateCaptures() const {
        std::vector<Move> captures;
        auto allMoves = generateMoves();
        for (const auto& move : allMoves) {
            if (isCapture(move)) captures.push_back(move);
        }
        return captures;
    }
    
    const std::vector<Move>& moveStack() const { return moveStack_; }
    
    std::vector<std::pair<Square, Piece>> pieceList() const {
        std::vector<std::pair<Square, Piece>> list;
        for (int sq = 0; sq < 64; ++sq) {
            auto piece = pieceAt(static_cast<Square>(sq));
            if (piece.type != PieceType::NONE) {
                list.emplace_back(static_cast<Square>(sq), piece);
            }
        }
        return list;
    }
    
    int popcount() const { return __builtin_popcountll(occupied_); }
    
    inline bool isInCheck(Color color) const {
        int kingSq = __builtin_ctzll(pieces_[static_cast<int>(color)][5]);
        return isSquareAttacked(static_cast<Square>(kingSq), 
               color == Color::WHITE ? Color::BLACK : Color::WHITE);
    }
    
    bool hasNonPawnMaterial(Color color) const {
        return (pieces_[static_cast<int>(color)][1] | pieces_[static_cast<int>(color)][2] | 
                pieces_[static_cast<int>(color)][3] | pieces_[static_cast<int>(color)][4]) != 0;
    }
};

// Opening Book
struct BookEntry {
    uint64_t key;
    uint16_t move;
    uint16_t weight;
    uint32_t learn;
};

class Book {
private:
    std::vector<BookEntry> entries;
    std::mt19937 rng;
    
    uint64_t computeKey(const Board& board) const {
        uint64_t key = 0;
        auto pieces = board.pieceList();
        for (const auto& [sq, piece] : pieces) {
            key ^= (static_cast<uint64_t>(static_cast<int>(piece.type) * 2 + 
                     static_cast<int>(piece.color)) << 8) ^ static_cast<uint64_t>(sq);
        }
        return key;
    }
    
    Move decodeMove(uint16_t move16, const Board&) const {
        int from = ((move16 >> 6) & 0x3F) ^ 0x38;
        int to = (move16 & 0x3F) ^ 0x38;
        int promo = (move16 >> 12) & 0x7;
        
        PieceType ptype = PieceType::NONE;
        if (promo == 1) ptype = PieceType::KNIGHT;
        else if (promo == 2) ptype = PieceType::BISHOP;
        else if (promo == 3) ptype = PieceType::ROOK;
        else if (promo == 4) ptype = PieceType::QUEEN;
        
        return Move(static_cast<Square>(from), static_cast<Square>(to), ptype);
    }
    
public:
    Book() : rng(std::random_device{}()) {}
    
    bool load(const std::string& path) {
        std::ifstream file(path, std::ios::binary);
        if (!file) return false;
        
        entries.clear();
        BookEntry entry;
        while (file.read(reinterpret_cast<char*>(&entry), sizeof(entry))) {
            entries.push_back(entry);
        }
        
        if (!entries.empty()) {
            std::cerr << "info string Opening book loaded: " << path << std::endl;
        }
        return !entries.empty();
    }
    
    bool isLoaded() const { return !entries.empty(); }
    
    std::optional<Move> getMove(const Board& board) {
        if (board.moveStack().size() > 20 || entries.empty()) return std::nullopt;
        
        uint64_t key = computeKey(board);
        std::vector<BookEntry> matches;
        
        for (const auto& entry : entries) {
            if (entry.key == key) matches.push_back(entry);
        }
        
        if (matches.empty()) return std::nullopt;
        
        uint16_t totalWeight = 0;
        for (const auto& m : matches) totalWeight += m.weight;
        
        std::uniform_int_distribution<> dist(0, totalWeight - 1);
        uint16_t r = dist(rng);
        
        for (const auto& m : matches) {
            if (r < m.weight) return decodeMove(m.move, board);
            r -= m.weight;
        }
        
        return std::nullopt;
    }
};

// Evaluation
using Score = int;
constexpr Score CENTER_BONUS = 20;
constexpr Score BISHOP_PAIR_BONUS = 30;
constexpr Score ROOK_OPEN_FILE_BONUS = 25;
constexpr Score DOUBLED_PAWN_PENALTY = 15;
constexpr Score ISOLATED_PAWN_PENALTY = 20;

struct Evaluator {
    std::array<int, 6> pieceValues = {100, 320, 330, 500, 900, 20000};
    
    const std::array<int, 64> pawnTable = {
         0,  0,  0,  0,  0,  0,  0,  0,
         5,  5,  5,  5,  5,  5,  5,  5,
         2,  2,  3,  3,  3,  3,  2,  2,
         0,  0,  0,  5,  5,  0,  0,  0,
         0,  0,  0, -5, -5,  0,  0,  0,
        -2, -2, -3, -10,-10, -3, -2, -2,
        -5, -5, -5, -15,-15, -5, -5, -5,
         0,  0,  0,  0,  0,  0,  0,  0
    };
    
    bool isPassedPawn(const Board& board, Square sq, Color color) const {
        int rank = static_cast<int>(sq) / 8;
        int file = static_cast<int>(sq) % 8;
        Color enemy = (color == Color::WHITE) ? Color::BLACK : Color::WHITE;
        uint64_t enemyPawns = board.getBitboard(PieceType::PAWN, enemy);
        
        uint64_t blockMask = 0;
        if (color == Color::WHITE) {
            for (int r = rank + 1; r < 8; ++r) {
                for (int f = std::max(0, file-1); f <= std::min(7, file+1); ++f) {
                    blockMask |= (1ULL << (r * 8 + f));
                }
            }
        } else {
            for (int r = rank - 1; r >= 0; --r) {
                for (int f = std::max(0, file-1); f <= std::min(7, file+1); ++f) {
                    blockMask |= (1ULL << (r * 8 + f));
                }
            }
        }
        return (enemyPawns & blockMask) == 0;
    }
    
    int evaluateKingSafety(const Board& board, Color color, int kingSq) const {
        int safety = 0;
        int rank = kingSq / 8;
        int file = kingSq % 8;
        
        uint64_t ownPawns = board.getBitboard(PieceType::PAWN, color);
        uint64_t shieldMask = 0;
        
        if (color == Color::WHITE) {
            if (file > 0) shieldMask |= (1ULL << ((rank + 1) * 8 + (file - 1)));
            shieldMask |= (1ULL << ((rank + 1) * 8 + file));
            if (file < 7) shieldMask |= (1ULL << ((rank + 1) * 8 + (file + 1)));
        } else {
            if (file > 0) shieldMask |= (1ULL << ((rank - 1) * 8 + (file - 1)));
            shieldMask |= (1ULL << ((rank - 1) * 8 + file));
            if (file < 7) shieldMask |= (1ULL << ((rank - 1) * 8 + (file + 1)));
        }
        
        int shieldPawns = popcount(ownPawns & shieldMask);
        safety += shieldPawns * 20;
        
        Color enemy = (color == Color::WHITE) ? Color::BLACK : Color::WHITE;
        uint64_t kingArea = Attacks::kingAttacks(static_cast<Square>(kingSq));
        int attacks = popcount(kingArea & board.getBitboard(PieceType::PAWN, enemy));
        safety -= attacks * 15;
        
        return safety;
    }
    
    int evaluateMobility(const Board& board, Color color) const {
        int mobility = 0;
        Color them = (color == Color::WHITE) ? Color::BLACK : Color::WHITE;
        uint64_t occ = board.occupied();
        uint64_t enemy = 0;
        for (int p = 0; p < 6; ++p) enemy |= board.getBitboard(static_cast<PieceType>(p), them);
        
        uint64_t knights = board.getBitboard(PieceType::KNIGHT, color);
        while (knights) {
            int sq = lsbIndex(knights);
            knights &= knights - 1;
            uint64_t moves = Attacks::knightAttacks(static_cast<Square>(sq));
            mobility += popcount(moves & ~occ);
        }
        
        uint64_t bishops = board.getBitboard(PieceType::BISHOP, color);
        while (bishops) {
            int sq = lsbIndex(bishops);
            bishops &= bishops - 1;
            uint64_t moves = Attacks::bishopAttacks(static_cast<Square>(sq), occ);
            mobility += popcount(moves & ~occ);
        }
        
        uint64_t rooks = board.getBitboard(PieceType::ROOK, color);
        while (rooks) {
            int sq = lsbIndex(rooks);
            rooks &= rooks - 1;
            uint64_t moves = Attacks::rookAttacks(static_cast<Square>(sq), occ);
            mobility += popcount(moves & ~occ);
        }
        
        uint64_t queens = board.getBitboard(PieceType::QUEEN, color);
        while (queens) {
            int sq = lsbIndex(queens);
            queens &= queens - 1;
            uint64_t moves = Attacks::queenAttacks(static_cast<Square>(sq), occ);
            mobility += popcount(moves & ~occ);
        }
        
        return mobility;
    }
    
    Score evaluate(const Board& board) const {
        Score score = 0;
        const std::array<Square, 4> center = {Square::D4, Square::E4, Square::D5, Square::E5};
        
        for (int c = 0; c < 2; ++c) {
            if (popcount(board.getBitboard(PieceType::BISHOP, static_cast<Color>(c))) >= 2) {
                score += (c == 0 ? BISHOP_PAIR_BONUS : -BISHOP_PAIR_BONUS);
            }
        }
        
        for (const auto& [sq, piece] : board.pieceList()) {
            if (piece.type == PieceType::NONE) continue;
            
            Score value = pieceValues[static_cast<int>(piece.type)];
            int file = static_cast<int>(sq) % 8;
            int rank = static_cast<int>(sq) / 8;
            
            if (std::find(center.begin(), center.end(), sq) != center.end()) {
                value += CENTER_BONUS;
            }
            
            if (piece.type == PieceType::PAWN) {
                int tableValue = pawnTable[static_cast<int>(sq)];
                if (piece.color == Color::BLACK) {
                    tableValue = pawnTable[63 - static_cast<int>(sq)];
                    tableValue = -tableValue;
                }
                value += tableValue;
                
                if (isPassedPawn(board, sq, piece.color)) {
                    int bonus = (piece.color == Color::WHITE) ? 
                                ((rank - 1) * 20) : ((6 - rank) * 20);
                    value += bonus;
                }
                
                uint64_t fileMask = 0x0101010101010101ULL << file;
                if (popcount(board.getBitboard(PieceType::PAWN, piece.color) & fileMask) > 1) {
                    value -= DOUBLED_PAWN_PENALTY;
                }
                
                uint64_t adjacentFiles = 0;
                if (file > 0) adjacentFiles |= (0x0101010101010101ULL << (file-1));
                if (file < 7) adjacentFiles |= (0x0101010101010101ULL << (file+1));
                
                if ((board.getBitboard(PieceType::PAWN, piece.color) & adjacentFiles) == 0) {
                    value -= ISOLATED_PAWN_PENALTY;
                }
            }
            
            if (piece.type == PieceType::ROOK) {
                uint64_t fileMask = 0x0101010101010101ULL << file;
                if ((board.getBitboard(PieceType::PAWN, piece.color) & fileMask) == 0) {
                    value += ROOK_OPEN_FILE_BONUS;
                }
            }
            
            score += (piece.color == Color::WHITE ? value : -value);
        }
        
        for (int c = 0; c < 2; ++c) {
            Color color = static_cast<Color>(c);
            int kingSq = __builtin_ctzll(board.getBitboard(PieceType::KING, color));
            int kingSafety = evaluateKingSafety(board, color, kingSq);
            int mobility = evaluateMobility(board, color) / 4;
            
            score += (color == Color::WHITE ? kingSafety + mobility : -kingSafety - mobility);
        }
        
        return board.turn() == Color::WHITE ? score : -score;
    }
};

// Search
using Depth = int;
constexpr Score INFINITY_SCORE = 30000;
constexpr Depth MAX_KILLER_DEPTH = 30;
constexpr Depth MAX_QUIESCENCE_PLY = 30;

struct SearchStats {
    int64_t nodes = 0;
    int64_t qNodes = 0;
    std::chrono::steady_clock::time_point startTime;
    Depth depth = 0;
	int seldepth = 0; 
    int64_t maxTimeMs = INT64_MAX;
    std::atomic<bool> stopSearch{false};
    
    void start(int64_t maxTime = INT64_MAX) {
        nodes = 0;
        qNodes = 0;
		seldepth = 0;
        maxTimeMs = maxTime;
        stopSearch = false;
        startTime = std::chrono::steady_clock::now();
    }
    
    void addNode(bool quiescence = false) {
        if (quiescence) qNodes++;
        else nodes++;
    }
    
    int64_t nps() const {
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - startTime).count();
        return (nodes + qNodes) * 1000 / std::max<int64_t>(ms, 1);
    }
    
    int64_t timeMs() const {
        return std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - startTime).count();
    }
    
    bool checkTime() {
        if (stopSearch.load(std::memory_order_relaxed)) return true;
        if (maxTimeMs == INT64_MAX) return false;
        
        if (((nodes + qNodes) & 0x7FF) != 0) return false;
        
        if (timeMs() >= maxTimeMs) {
            stopSearch.store(true, std::memory_order_relaxed);
            return true;
        }
        return false;
    }
};

class Searcher {
private:
    Board& board;
    Evaluator eval;
    std::array<std::array<std::optional<Move>, 2>, MAX_KILLER_DEPTH> killers_;
    std::array<std::array<int, 64>, 64> history_;
    SearchStats stats;
    
    struct TTEntry {
        uint64_t key = 0;
        Move move;
        Score score = 0;
        Depth depth = 0;
        uint8_t flag = 0;
    };
    std::vector<TTEntry> tt;
    const uint64_t ttSize = 1 << 21;
    
    void clearTT() { std::fill(tt.begin(), tt.end(), TTEntry()); }
    
    void storeTT(uint64_t key, Move move, Score score, Depth depth, uint8_t flag) {
        TTEntry& entry = tt[key % tt.size()];
        if (depth >= entry.depth || entry.key == 0) {
            entry.key = key; entry.move = move; entry.score = score;
            entry.depth = depth; entry.flag = flag;
        }
    }
    
    int mvvLvaScore(const Move& move) const {
        if (!board.isCapture(move)) return 0;
        auto victim = board.pieceAt(move.to);
        auto aggressor = board.pieceAt(move.from);
        if (victim.type != PieceType::NONE && aggressor.type != PieceType::NONE) {
            return eval.pieceValues[static_cast<int>(victim.type)] * 10 - 
                   eval.pieceValues[static_cast<int>(aggressor.type)];
        }
        return 0;
    }
    
    int scoreMove(const Move& move, Depth ply, uint64_t hash) const {
		board.makeMove(move);
		bool givesCheckmate = board.isCheckmate();
		board.unmakeMove();
		if (givesCheckmate) return 300000;
        const TTEntry* entry = &tt[hash % tt.size()];
        if (entry->key == hash && entry->move == move) return 200000;
        
        int captureScore = mvvLvaScore(move);
        if (captureScore != 0) return 100000 + captureScore;
        
        if (move.promotion != PieceType::NONE) {
            return 90000 + eval.pieceValues[static_cast<int>(move.promotion)];
        }
        
        if (ply < MAX_KILLER_DEPTH) {
            if (killers_[ply][0] && *killers_[ply][0] == move) return 50000;
            if (killers_[ply][1] && *killers_[ply][1] == move) return 40000;
        }
        
        return history_[static_cast<int>(move.from)][static_cast<int>(move.to)];
    }
    
    std::vector<Move> orderMoves(const std::vector<Move>& moves, Depth ply, uint64_t hash) const {
        std::vector<std::pair<int, Move>> scored;
        scored.reserve(moves.size());
        for (const auto& move : moves) {
            scored.emplace_back(scoreMove(move, ply, hash), move);
        }
        std::sort(scored.begin(), scored.end(),
            [](const auto& a, const auto& b) { return a.first > b.first; });
        
        std::vector<Move> ordered;
        ordered.reserve(moves.size());
        for (const auto& p : scored) ordered.push_back(p.second);
        return ordered;
    }
    
    Score quiescence(Score alpha, Score beta, Depth ply) {
        stats.addNode(true);
		stats.seldepth = std::max(stats.seldepth, ply); 
        
        // Check time frequently
        if (stats.checkTime()) return alpha;
        
        bool inCheck = board.isInCheck(board.turn());
        Score standPat = eval.evaluate(board);
        
        if (!inCheck) {
            if (standPat >= beta) return beta;
            if (alpha < standPat) alpha = standPat;
        }
        
        if (ply >= MAX_QUIESCENCE_PLY) return alpha;
        
        auto moves = inCheck ? board.generateMoves() : board.generateCaptures();
        if (moves.empty()) return inCheck ? -INFINITY_SCORE + ply : standPat;
        
        auto ordered = orderMoves(moves, ply, board.computeHash());
        for (const auto& move : ordered) {
            if (stats.stopSearch.load(std::memory_order_relaxed)) break;
            
            board.makeMove(move);
            Score score = -quiescence(-beta, -alpha, ply + 1);
            board.unmakeMove();
            if (score >= beta) return beta;
            if (score > alpha) alpha = score;
        }
        return alpha;
    }
    
    std::pair<Score, std::optional<Move>> negamax(Depth depth, Score alpha, Score beta, Depth ply) {
        stats.addNode();
		stats.seldepth = std::max(stats.seldepth, ply);
        
        if (stats.checkTime()) return {alpha, std::nullopt};
        
        if (depth <= 0) return {quiescence(alpha, beta, ply), std::nullopt};
		bool inCheck = board.isInCheck(board.turn());
		if (inCheck) depth++;  // Extend by 1 ply
        
        uint64_t hash = board.computeHash();
        
        TTEntry* entry = &tt[hash % tt.size()];
        if (entry->key == hash && entry->depth >= depth) {
            if (entry->flag == 1) return {entry->score, entry->move};
            if (entry->flag == 2 && entry->score >= beta) return {beta, entry->move};
            if (entry->flag == 3 && entry->score <= alpha) return {alpha, entry->move};
        }
        
        if (depth >= 3 && !board.isInCheck(board.turn()) && board.hasNonPawnMaterial(board.turn())) {
            board.makeNullMove();
            auto [nullScore, _] = negamax(depth - 3, -beta, -beta + 1, ply + 1);
            board.unmakeNullMove();
            if (-nullScore >= beta) return {beta, std::nullopt};
        }
        
        if (board.isCheckmate()) return {-INFINITY_SCORE + ply, std::nullopt};
		if (board.isStalemate() || board.isInsufficientMaterial()) return {0, std::nullopt};
        
        Score bestScore = -INFINITY_SCORE;
        std::optional<Move> bestMove;
        Score alphaOrig = alpha;
        
		auto moves = board.generateMoves();
		if (moves.empty()) {
			return {board.isInCheck(board.turn()) ? -INFINITY_SCORE + ply : 0, std::nullopt};
		}
        
        auto ordered = orderMoves(moves, ply, hash);
        int moveCount = 0;
        
        for (const auto& move : ordered) {
            if (stats.stopSearch.load(std::memory_order_relaxed)) break;
            
            bool isCapture = board.isCapture(move);
            bool isPromotion = (move.promotion != PieceType::NONE);
            
            Depth reduction = 0;
            if (depth >= 3 && moveCount >= 3 && !isCapture && !isPromotion && !board.isInCheck(board.turn())) {
                reduction = 1;
            }
            
            board.makeMove(move);
            Score score;
            
            if (reduction > 0) {
                auto [reducedScore, _] = negamax(depth - reduction - 1, -beta, -alpha, ply + 1);
                score = -reducedScore;
                if (score > alpha) {
                    auto [fullScore, _] = negamax(depth - 1, -beta, -alpha, ply + 1);
                    score = -fullScore;
                }
            } else {
                auto [searchScore, _] = negamax(depth - 1, -beta, -alpha, ply + 1);
                score = -searchScore;
            }
            board.unmakeMove();
            
            moveCount++;
            
            if (score > bestScore) {
                bestScore = score;
                bestMove = move;
            }
            
            if (score > alpha) {
                alpha = score;
                if (!isCapture && ply < MAX_KILLER_DEPTH) {
                    if (!killers_[ply][0] || *killers_[ply][0] != move) {
                        killers_[ply][1] = killers_[ply][0];
                        killers_[ply][0] = move;
                    }
                }
            }
            
            if (alpha >= beta) {
                if (!isCapture) {
                    history_[static_cast<int>(move.from)][static_cast<int>(move.to)] += depth * depth;
                }
                break;
            }
        }
        
        uint8_t flag = (bestScore <= alphaOrig) ? 3 : (bestScore >= beta ? 2 : 1);
        storeTT(hash, bestMove.value_or(Move()), bestScore, depth, flag);
        
        return {bestScore, bestMove};
    }

public:
    explicit Searcher(Board& b) : board(b) {
        try {
            tt.resize(ttSize);
        } catch (const std::bad_alloc& e) {
            std::cerr << "Warning: TT allocation failed, using 256K entries" << std::endl;
            tt.resize(1 << 18);
        }
        clearTT();
        for (auto& k : killers_) {
            k[0] = std::nullopt;
            k[1] = std::nullopt;
        }
        for (auto& row : history_) row.fill(0);
    }
	
	int hashfull() const {
		int used = 0;
		const int sampleSize = std::min<int>(tt.size(), 1000);
		for (int i = 0; i < sampleSize; ++i) {
			if (tt[i].key != 0) used++;
		}
		return (used * 1000) / sampleSize; 
	}
    
    std::pair<std::optional<Move>, Depth> iterativeDeepening(Depth maxDepth, int64_t maxTimeMs) {
        stats.start(maxTimeMs);
        clearTT();
        for (auto& k : killers_) {
            k[0] = std::nullopt;
            k[1] = std::nullopt;
        }
        for (auto& row : history_) row.fill(0);
        
        std::optional<Move> bestMove;
        Score prevScore = 0;
        Depth finalDepth = 0;
        
        for (Depth currentDepth = 1; currentDepth <= maxDepth; ++currentDepth) {
            if (stats.checkTime()) break;
            
            stats.depth = currentDepth;
			stats.seldepth = 0;
            
            Score alpha = -INFINITY_SCORE;
            Score beta = INFINITY_SCORE;
            if (currentDepth >= 5) {
                alpha = prevScore - 50;
                beta = prevScore + 50;
            }
            
            auto [score, move] = negamax(currentDepth, alpha, beta, 0);
            
            if (stats.stopSearch.load(std::memory_order_relaxed)) {
                break;
            }
            
            if (score <= alpha || score >= beta) {
                auto [fullScore, fullMove] = negamax(currentDepth, -INFINITY_SCORE, INFINITY_SCORE, 0);
                score = fullScore;
                move = fullMove;
            }
            
            prevScore = score;
            if (move) bestMove = move;
            finalDepth = currentDepth;
            
            int64_t time = stats.timeMs();
            int64_t nps = stats.nps();
            std::cout << "info depth " << currentDepth
				      << " seldepth " << stats.seldepth
                      << " score cp " << score
                      << " nodes " << (stats.nodes + stats.qNodes)
                      << " nps " << nps
                      << " time " << time
					  << " hashfull " << hashfull();
            if (bestMove) std::cout << " pv " << bestMove->toUci();
            std::cout << std::endl;
            
            if (stats.checkTime()) break;
        }
        return {bestMove, finalDepth};
    }
};

// UCI
class UCIEngine {
private:
    Board board;
    Searcher searcher;
    Book book;
    Depth maxDepth = 20;
    int64_t wtime = 0, btime = 0;
    int64_t winc = 0, binc = 0; 
    int movestogo = 0;
    
    void handleUci() {
        std::cout << "id name Hunyadi 1.0\n";
        std::cout << "id author CiganySalesman\n";
        std::cout << "option name BookFile type string default book.bin\n";
        std::cout << "option name MaxDepth type spin default 20 min 1 max 30\n";
        std::cout << "uciok" << std::endl;
    }
    
    void handleIsReady() { std::cout << "readyok" << std::endl; }
    
    void handleNewGame() {
        board.reset();
        if (!book.isLoaded()) book.load("book.bin");
    }
    
    int64_t calculateMoveTime() {
        Color side = board.turn();
        int64_t timeLeft = (side == Color::WHITE) ? wtime : btime;
        int64_t increment = (side == Color::WHITE) ? winc : binc;
        
        if (timeLeft <= 0) return 300000;
        
        int movesRemaining = movestogo;
        if (movesRemaining <= 0) {
            int pieceCount = board.popcount();
            movesRemaining = (pieceCount > 20) ? 30 : 10;
        }
        
		int64_t baseTime = (timeLeft / std::max(1, movesRemaining)) * 120 / 100;
        
        int64_t incBonus = increment * 3 / 4;
        
        int64_t maxTime = timeLeft / 1.1;
        
        int64_t calculatedTime = std::min(maxTime, baseTime + incBonus);
        
        return std::max<int64_t>(100, std::min<int64_t>(calculatedTime, 600000));
    }
    
    void handlePosition(std::istringstream& iss) {
        std::string token;
        iss >> token;
        
        if (token == "startpos") {
            board.reset();
            if (iss >> token && token == "moves") {
                while (iss >> token) {
                    if (token.length() >= 4) {
                        int fromFile = token[0] - 'a';
                        int fromRank = token[1] - '1';
                        int toFile = token[2] - 'a';
                        int toRank = token[3] - '1';
                        
                        if (fromFile >= 0 && fromFile < 8 && fromRank >= 0 && fromRank < 8 &&
                            toFile >= 0 && toFile < 8 && toRank >= 0 && toRank < 8) {
                            
                            Square from = static_cast<Square>(fromRank * 8 + fromFile);
                            Square to = static_cast<Square>(toRank * 8 + toFile);
                            
                            PieceType promo = PieceType::NONE;
                            if (token.length() == 5) {
                                switch (token[4]) {
                                    case 'n': promo = PieceType::KNIGHT; break;
                                    case 'b': promo = PieceType::BISHOP; break;
                                    case 'r': promo = PieceType::ROOK; break;
                                    case 'q': promo = PieceType::QUEEN; break;
                                }
                            }
                            
                            Move move(from, to, promo);
                            auto legalMoves = board.generateMoves();
                            if (std::find(legalMoves.begin(), legalMoves.end(), move) != legalMoves.end()) {
                                board.makeMove(move);
                            }
                        }
                    }
                }
            }
        } else if (token == "fen") {
            std::string fen;
            for (int i = 0; i < 6; ++i) {
                iss >> token;
                fen += token + " ";
            }
            board.setFen(fen);
            
            if (iss >> token && token == "moves") {
                while (iss >> token) {
                    if (token.length() >= 4) {
                        int fromFile = token[0] - 'a';
                        int fromRank = token[1] - '1';
                        int toFile = token[2] - 'a';
                        int toRank = token[3] - '1';
                        
                        if (fromFile >= 0 && fromFile < 8 && fromRank >= 0 && fromRank < 8 &&
                            toFile >= 0 && toFile < 8 && toRank >= 0 && toRank < 8) {
                            
                            Square from = static_cast<Square>(fromRank * 8 + fromFile);
                            Square to = static_cast<Square>(toRank * 8 + toFile);
                            
                            PieceType promo = PieceType::NONE;
                            if (token.length() == 5) {
                                switch (token[4]) {
                                    case 'n': promo = PieceType::KNIGHT; break;
                                    case 'b': promo = PieceType::BISHOP; break;
                                    case 'r': promo = PieceType::ROOK; break;
                                    case 'q': promo = PieceType::QUEEN; break;
                                }
                            }
                            
                            Move move(from, to, promo);
                            auto legalMoves = board.generateMoves();
                            if (std::find(legalMoves.begin(), legalMoves.end(), move) != legalMoves.end()) {
                                board.makeMove(move);
                            }
                        }
                    }
                }
            }
        }
    }
    
    void handleGo(std::istringstream& iss) {
        std::string token;
        int64_t moveTime = -1; 
        
        wtime = 0; btime = 0;
        winc = 0; binc = 0;
        movestogo = 0;
        
        while (iss >> token) {
            if (token == "depth") {
                iss >> maxDepth;
            } else if (token == "movetime") {
                iss >> moveTime;
            } else if (token == "infinite") {
                moveTime = INT64_MAX;
            } else if (token == "wtime") {
                iss >> wtime;
            } else if (token == "btime") {
                iss >> btime;
            } else if (token == "winc") {
                iss >> winc;
            } else if (token == "binc") {
                iss >> binc;
            } else if (token == "movestogo") {
                iss >> movestogo;
            }
        }
        
        if (moveTime == -1) {
            moveTime = calculateMoveTime();
            std::cerr << "info string Time left: " << (board.turn() == Color::WHITE ? wtime : btime) 
                      << "ms, Moves remaining: " << (movestogo ? movestogo : (board.popcount() > 20 ? 30 : 10))
                      << ", Allocated: " << moveTime << "ms" << std::endl;
        }
        
        auto bookMove = book.getMove(board);
        if (bookMove) {
            std::cout << "bestmove " << bookMove->toUci() << std::endl;
            return;
        }
        
        auto [bestMove, finalDepth] = searcher.iterativeDeepening(maxDepth, moveTime);
        if (bestMove) {
            std::cout << "bestmove " << bestMove->toUci() << std::endl;
        } else {
            auto moves = board.generateMoves();
            if (!moves.empty()) std::cout << "bestmove " << moves[0].toUci() << std::endl;
            else std::cout << "bestmove 0000" << std::endl;
        }
    }
    
    void handleSetOption(std::istringstream& iss) {
        std::string token, name, value;
        iss >> token >> name >> token >> value;
        if (name == "MaxDepth") maxDepth = std::stoi(value);
        else if (name == "BookFile") book.load(value);
    }
    
public:
    UCIEngine() : board(), searcher(board) {}
    
    void loop() {
        std::string line;
        while (std::getline(std::cin, line)) {
            std::istringstream iss(line);
            std::string cmd;
            iss >> cmd;
            
            if (cmd == "uci") handleUci();
            else if (cmd == "isready") handleIsReady();
            else if (cmd == "ucinewgame") handleNewGame();
            else if (cmd == "position") handlePosition(iss);
            else if (cmd == "go") handleGo(iss);
            else if (cmd == "setoption") handleSetOption(iss);
            else if (cmd == "quit") break;
            
            std::cout.flush();
        }
    }
};

// Main
int main() {
    UCIEngine engine;
    engine.loop();
    return 0;
}