/*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2025 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef BITBOARD_H_INCLUDED
#define BITBOARD_H_INCLUDED

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstring>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <initializer_list>
#include <array>

#include "types.h"

namespace Stockfish {

namespace Bitboards {

void        init();
std::string pretty(Bitboard b);

}  // namespace Stockfish::Bitboards

constexpr Bitboard FileABB = 0x0101010101010101ULL;
constexpr Bitboard FileBBB = FileABB << 1;
constexpr Bitboard FileCBB = FileABB << 2;
constexpr Bitboard FileDBB = FileABB << 3;
constexpr Bitboard FileEBB = FileABB << 4;
constexpr Bitboard FileFBB = FileABB << 5;
constexpr Bitboard FileGBB = FileABB << 6;
constexpr Bitboard FileHBB = FileABB << 7;

constexpr Bitboard Rank1BB = 0xFF;
constexpr Bitboard Rank2BB = Rank1BB << (8 * 1);
constexpr Bitboard Rank3BB = Rank1BB << (8 * 2);
constexpr Bitboard Rank4BB = Rank1BB << (8 * 3);
constexpr Bitboard Rank5BB = Rank1BB << (8 * 4);
constexpr Bitboard Rank6BB = Rank1BB << (8 * 5);
constexpr Bitboard Rank7BB = Rank1BB << (8 * 6);
constexpr Bitboard Rank8BB = Rank1BB << (8 * 7);

extern uint8_t PopCnt16[1 << 16];
extern uint8_t SquareDistance[SQUARE_NB][SQUARE_NB];

extern Bitboard BetweenBB[SQUARE_NB][SQUARE_NB];
extern Bitboard LineBB[SQUARE_NB][SQUARE_NB];
extern Bitboard RayPassBB[SQUARE_NB][SQUARE_NB];

struct Mask {
    Bitboard diagonal;
    Bitboard antidiagonal;
    Bitboard vertical;
};

constexpr Bitboard square_bb(Square s) {
    assert(is_ok(s));
    return (1ULL << s);
}


// Overloads of bitwise operators between a Bitboard and a Square for testing
// whether a given bit is set in a bitboard, and for setting and clearing bits.

constexpr Bitboard  operator&(Bitboard b, Square s) { return b & square_bb(s); }
constexpr Bitboard  operator|(Bitboard b, Square s) { return b | square_bb(s); }
constexpr Bitboard  operator^(Bitboard b, Square s) { return b ^ square_bb(s); }
constexpr Bitboard& operator|=(Bitboard& b, Square s) { return b |= square_bb(s); }
constexpr Bitboard& operator^=(Bitboard& b, Square s) { return b ^= square_bb(s); }

constexpr Bitboard operator&(Square s, Bitboard b) { return b & s; }
constexpr Bitboard operator|(Square s, Bitboard b) { return b | s; }
constexpr Bitboard operator^(Square s, Bitboard b) { return b ^ s; }

constexpr Bitboard operator|(Square s1, Square s2) { return square_bb(s1) | s2; }

constexpr bool more_than_one(Bitboard b) { return b & (b - 1); }


// rank_bb() and file_bb() return a bitboard representing all the squares on
// the given file or rank.

constexpr Bitboard rank_bb(Rank r) { return Rank1BB << (8 * r); }

constexpr Bitboard rank_bb(Square s) { return rank_bb(rank_of(s)); }

constexpr Bitboard file_bb(File f) { return FileABB << f; }

constexpr Bitboard file_bb(Square s) { return file_bb(file_of(s)); }


// Moves a bitboard one or two steps as specified by the direction D
template<Direction D>
constexpr Bitboard shift(Bitboard b) {
    return D == NORTH         ? b << 8
         : D == SOUTH         ? b >> 8
         : D == NORTH + NORTH ? b << 16
         : D == SOUTH + SOUTH ? b >> 16
         : D == EAST          ? (b & ~FileHBB) << 1
         : D == WEST          ? (b & ~FileABB) >> 1
         : D == NORTH_EAST    ? (b & ~FileHBB) << 9
         : D == NORTH_WEST    ? (b & ~FileABB) << 7
         : D == SOUTH_EAST    ? (b & ~FileHBB) >> 7
         : D == SOUTH_WEST    ? (b & ~FileABB) >> 9
                              : 0;
}


// Returns the squares attacked by pawns of the given color
// from the squares in the given bitboard.
template<Color C>
constexpr Bitboard pawn_attacks_bb(Bitboard b) {
    return C == WHITE ? shift<NORTH_WEST>(b) | shift<NORTH_EAST>(b)
                      : shift<SOUTH_WEST>(b) | shift<SOUTH_EAST>(b);
}


// Returns a bitboard representing an entire line (from board edge
// to board edge) that intersects the two given squares. If the given squares
// are not on a same file/rank/diagonal, the function returns 0. For instance,
// line_bb(SQ_C4, SQ_F7) will return a bitboard with the A2-G8 diagonal.
inline Bitboard line_bb(Square s1, Square s2) {

    assert(is_ok(s1) && is_ok(s2));
    return LineBB[s1][s2];
}


// Returns a bitboard representing the squares in the semi-open
// segment between the squares s1 and s2 (excluding s1 but including s2). If the
// given squares are not on a same file/rank/diagonal, it returns s2. For instance,
// between_bb(SQ_C4, SQ_F7) will return a bitboard with squares D5, E6 and F7, but
// between_bb(SQ_E6, SQ_F8) will return a bitboard with the square F8. This trick
// allows to generate non-king evasion moves faster: the defending piece must either
// interpose itself to cover the check or capture the checking piece.
inline Bitboard between_bb(Square s1, Square s2) {

    assert(is_ok(s1) && is_ok(s2));
    return BetweenBB[s1][s2];
}

// distance() functions return the distance between x and y, defined as the
// number of steps for a king in x to reach y.

template<typename T1 = Square>
inline int distance(Square x, Square y);

template<>
inline int distance<File>(Square x, Square y) {
    return std::abs(file_of(x) - file_of(y));
}

template<>
inline int distance<Rank>(Square x, Square y) {
    return std::abs(rank_of(x) - rank_of(y));
}

template<>
inline int distance<Square>(Square x, Square y) {
    return SquareDistance[x][y];
}

inline int edge_distance(File f) { return std::min(f, File(FILE_H - f)); }


constexpr int constexpr_popcount(Bitboard b) {
    b = b - ((b >> 1) & 0x5555555555555555ULL);
    b = (b & 0x3333333333333333ULL) + ((b >> 2) & 0x3333333333333333ULL);
    b = (b + (b >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return static_cast<int>((b * 0x0101010101010101ULL) >> 56);
}

// Counts the number of non-zero bits in a bitboard.
inline int popcount(Bitboard b) {

#ifndef USE_POPCNT

    std::uint16_t indices[4];
    std::memcpy(indices, &b, sizeof(b));
    return PopCnt16[indices[0]] + PopCnt16[indices[1]] + PopCnt16[indices[2]]
         + PopCnt16[indices[3]];

#elif defined(_MSC_VER)

    return int(_mm_popcnt_u64(b));

#else  // Assumed gcc or compatible compiler

    return __builtin_popcountll(b);

#endif
}

// Returns the least significant bit in a non-zero bitboard.
inline Square lsb(Bitboard b) {
    assert(b);

#if defined(__GNUC__)  // GCC, Clang, ICX

    return Square(__builtin_ctzll(b));

#elif defined(_MSC_VER)
    #ifdef _WIN64  // MSVC, WIN64

    unsigned long idx;
    _BitScanForward64(&idx, b);
    return Square(idx);

    #else  // MSVC, WIN32
    unsigned long idx;

    if (b & 0xffffffff)
    {
        _BitScanForward(&idx, int32_t(b));
        return Square(idx);
    }
    else
    {
        _BitScanForward(&idx, int32_t(b >> 32));
        return Square(idx + 32);
    }
    #endif
#else  // Compiler is neither GCC nor MSVC compatible
    #error "Compiler not supported."
#endif
}

// Returns the most significant bit in a non-zero bitboard.
inline Square msb(Bitboard b) {
    assert(b);

#if defined(__GNUC__)  // GCC, Clang, ICX

    return Square(63 ^ __builtin_clzll(b));

#elif defined(_MSC_VER)
    #ifdef _WIN64  // MSVC, WIN64

    unsigned long idx;
    _BitScanReverse64(&idx, b);
    return Square(idx);

    #else  // MSVC, WIN32

    unsigned long idx;

    if (b >> 32)
    {
        _BitScanReverse(&idx, int32_t(b >> 32));
        return Square(idx + 32);
    }
    else
    {
        _BitScanReverse(&idx, int32_t(b));
        return Square(idx);
    }
    #endif
#else  // Compiler is neither GCC nor MSVC compatible
    #error "Compiler not supported."
#endif
}

// Returns the bitboard of the least significant
// square of a non-zero bitboard. It is equivalent to square_bb(lsb(bb)).
inline Bitboard least_significant_square_bb(Bitboard b) {
    assert(b);
    return b & -b;
}

// Finds and clears the least significant bit in a non-zero bitboard.
inline Square pop_lsb(Bitboard& b) {
    assert(b);
    const Square s = lsb(b);
    b &= b - 1;
    return s;
}

namespace Bitboards {
// Returns the bitboard of target square for the given step
// from the given square. If the step is off the board, returns empty bitboard.
constexpr Bitboard safe_destination(Square s, int step) {
    constexpr auto abs = [](int v) { return v < 0 ? -v : v; };
    Square         to  = Square(s + step);
    return is_ok(to) && abs(file_of(s) - file_of(to)) <= 2 ? square_bb(to) : Bitboard(0);
}

constexpr auto Masks = []() constexpr {
    int r{}, f{}, i{}, j{}, y{};
    int d[64]{};

    std::array<Mask, 64> MASK{};

    for (int x = 0; x < 64; ++x) {
        for (y = 0; y < 64; ++y) d[y] = 0;
        // directions
        for (i = -1; i <= 1; ++i)
            for (j = -1; j <= 1; ++j) {
                if (i == 0 && j == 0) continue;
                f = x & 07;
                r = x >> 3;
                for (r += i, f += j; 0 <= r && r < 8 && 0 <= f && f < 8; r += i, f += j) {
                    y = 8 * r + f;
                    d[y] = 8 * i + j;
                }
            }

        // uint64_t mask
        Mask& mask = MASK[x];
        for (y = x - 9; y >= 0 && d[y] == -9; y -= 9) mask.diagonal |= (1ull << y);
        for (y = x + 9; y < 64 && d[y] == 9; y += 9) mask.diagonal |= (1ull << y);

        for (y = x - 7; y >= 0 && d[y] == -7; y -= 7) mask.antidiagonal |= (1ull << y);
        for (y = x + 7; y < 64 && d[y] == 7; y += 7) mask.antidiagonal |= (1ull << y);

        for (y = x - 8; y >= 0; y -= 8) mask.vertical |= (1ull << y);
        for (y = x + 8; y < 64; y += 8) mask.vertical |= (1ull << y);
    }
    return MASK;
}();

constexpr auto RankAttacks = []() constexpr {
    std::array<uint8_t, 512> rank_attack{};

    for (int x = 0; x < 64; ++x) {
        for (int f = 0; f < 8; ++f) {
            int o = 2 * x;
            int x2{}, y2{};
            int b{};

            y2 = 0;
            for (x2 = f - 1; x2 >= 0; --x2) {
                b = 1 << x2;
                y2 |= b;
                if ((o & b) == b) break;
            }
            for (x2 = f + 1; x2 < 8; ++x2) {
                b = 1 << x2;
                y2 |= b;
                if ((o & b) == b) break;
            }
            rank_attack[x * 8ull + f] = y2;
        }
    }
    return rank_attack;
}();

static constexpr uint64_t bit_bswap_constexpr(uint64_t b) {
    b = ((b >> 8) & 0x00FF00FF00FF00FFULL) | ((b << 8) & 0xFF00FF00FF00FF00ULL);
    b = ((b >> 16) & 0x0000FFFF0000FFFFULL) | ((b << 16) & 0xFFFF0000FFFF0000ULL);
    b = ((b >> 32) & 0x00000000FFFFFFFFULL) | ((b << 32) & 0xFFFFFFFF00000000ULL);
    return b;
}

constexpr uint64_t bit_bswap(uint64_t b) {
#if defined(_MSC_VER)
    return _byteswap_uint64(b);
#elif defined(__GNUC__)
    return __builtin_bswap64(b);
#else
    return bit_bswap_constexpr(b);
#endif
}

static constexpr uint64_t attack(uint64_t pieces, uint32_t x, uint64_t mask) {
    uint64_t o = pieces & mask;
    return ((o - (1ull << x)) ^ bit_bswap(bit_bswap(o) - (0x8000000000000000ull >> x))) & mask; //Daniel 28.04.2022 - Faster shift. Replaces (1ull << (s ^ 56))
}

static constexpr uint64_t horizontal_attack(uint64_t pieces, uint32_t x) {
    uint32_t file_mask = x & 7;
    uint32_t rank_mask = x & 56;
    uint64_t o = (pieces >> rank_mask) & 126;

    return ((uint64_t)RankAttacks[o * 4 + file_mask]) << rank_mask;
}

static constexpr uint64_t vertical_attack(uint64_t occ, uint32_t sq) {
    return attack(occ, sq, Masks[sq].vertical);
}

static constexpr uint64_t diagonal_attack(uint64_t occ, uint32_t sq) {
    return attack(occ, sq, Masks[sq].diagonal);
}

static constexpr uint64_t antidiagonal_attack(uint64_t occ, uint32_t sq) {
    return attack(occ, sq, Masks[sq].antidiagonal);
}

static constexpr uint64_t bishop_attack(Square sq, Bitboard occ) {
    return diagonal_attack(occ, sq) | antidiagonal_attack(occ, sq);
}

static constexpr uint64_t rook_attack(Square sq, Bitboard occ) {
    return vertical_attack(occ, sq) | horizontal_attack(occ, sq);
}

constexpr Bitboard knight_attack(Square sq) {
    Bitboard b = {};
    for (int step : {-17, -15, -10, -6, 6, 10, 15, 17})
        b |= safe_destination(sq, step);
    return b;
}

constexpr Bitboard king_attack(Square sq) {
    Bitboard b = {};
    for (int step : {-9, -8, -7, -1, 1, 7, 8, 9})
        b |= safe_destination(sq, step);
    return b;
}

constexpr Bitboard pseudo_attacks(PieceType pt, Square sq) {
    switch (pt)
    {
    case ROOK :
        return rook_attack(sq, 0);
    case BISHOP :
        return bishop_attack(sq, 0);
    case QUEEN :
        return rook_attack(sq, 0) | bishop_attack(sq, 0);
    case KNIGHT :
        return knight_attack(sq);
    case KING :
        return king_attack(sq);
    default :
        assert(false);
        return 0;
    }
}

}

inline constexpr auto PseudoAttacks = []() constexpr {
    std::array<std::array<Bitboard, SQUARE_NB>, PIECE_TYPE_NB> attacks{};

    for (Square s1 = SQ_A1; s1 <= SQ_H8; ++s1)
    {
        attacks[WHITE][s1] = pawn_attacks_bb<WHITE>(square_bb(s1));
        attacks[BLACK][s1] = pawn_attacks_bb<BLACK>(square_bb(s1));

        attacks[KING][s1]   = Bitboards::pseudo_attacks(KING, s1);
        attacks[KNIGHT][s1] = Bitboards::pseudo_attacks(KNIGHT, s1);
        attacks[QUEEN][s1] = attacks[BISHOP][s1] = Bitboards::pseudo_attacks(BISHOP, s1);
        attacks[QUEEN][s1] |= attacks[ROOK][s1]  = Bitboards::pseudo_attacks(ROOK, s1);
    }

    return attacks;
}();


// Returns the pseudo attacks of the given piece type
// assuming an empty board.
template<PieceType Pt>
inline Bitboard attacks_bb(Square s, Color c = COLOR_NB) {

    assert((Pt != PAWN || c < COLOR_NB) && (is_ok(s)));
    return Pt == PAWN ? PseudoAttacks[c][s] : PseudoAttacks[Pt][s];
}


// Returns the attacks by the given piece
// assuming the board is occupied according to the passed Bitboard.
// Sliding piece attacks do not continue passed an occupied square.
template<PieceType Pt>
inline Bitboard attacks_bb(Square s, Bitboard occupied) {

    assert((Pt != PAWN) && (is_ok(s)));

    switch (Pt)
    {
        case ROOK :
            return Bitboards::rook_attack(s, occupied);
        case BISHOP :
            return Bitboards::bishop_attack(s, occupied);
        case QUEEN :
            return Bitboards::rook_attack(s, occupied) | Bitboards::bishop_attack(s, occupied);
    default :
        return PseudoAttacks[Pt][s];
    }
}

// Returns the attacks by the given piece
// assuming the board is occupied according to the passed Bitboard.
// Sliding piece attacks do not continue passed an occupied square.
inline Bitboard attacks_bb(PieceType pt, Square s, Bitboard occupied) {

    assert((pt != PAWN) && (is_ok(s)));

    switch (pt)
    {
    case BISHOP :
        return attacks_bb<BISHOP>(s, occupied);
    case ROOK :
        return attacks_bb<ROOK>(s, occupied);
    case QUEEN :
        return attacks_bb<BISHOP>(s, occupied) | attacks_bb<ROOK>(s, occupied);
    default :
        return PseudoAttacks[pt][s];
    }
}

inline Bitboard attacks_bb(Piece pc, Square s) {
    if (type_of(pc) == PAWN)
        return PseudoAttacks[color_of(pc)][s];

    return PseudoAttacks[type_of(pc)][s];
}


inline Bitboard attacks_bb(Piece pc, Square s, Bitboard occupied) {
    if (type_of(pc) == PAWN)
        return PseudoAttacks[color_of(pc)][s];

    return attacks_bb(type_of(pc), s, occupied);
}

}  // namespace Stockfish

#endif  // #ifndef BITBOARD_H_INCLUDED
