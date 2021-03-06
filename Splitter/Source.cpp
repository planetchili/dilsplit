#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include <iostream>
#include "FrameTimer.h"
#include <inttypes.h>
#include <intrin.h>
#include <fstream>

class Bignum
{
public:
	Bignum( unsigned long long number = 0ull )
	{
		bits.push_back( number );
	}
	Bignum( const std::string& number )
	{
		// preallocate memory for parsing work
		const size_t estimated_bits = number.size() / 3u;
		bits.reserve( estimated_bits / 64 + 1 );

		auto i = number.cbegin();
		const auto e = number.cend();
		// while there are 19 or more digits remaining
		for( ; e - i >= 19; i += 19 )
		{
			auto value = 0ull;
			// loop through digits, convert to single ull
			for( auto j = i,e = i + 19; j != e; j++ )
			{
				assert( *j >= '0' && *j <= '9' );
				value *= 10ull;
				value += unsigned long long( *j - '0' );
			}
			// push ull digits to Bignum
			*this *= pow[19];
			*this += value;
		}
		// convert remaining digits
		auto value = 0ull;
		for( auto j = i; j != e; j++ )
		{
			assert( *j >= '0' && *j <= '9' );
			value *= 10ull;
			value += unsigned long long( *j - '0' );
		}
		// push ull digits to Bignum
		*this *= pow[int( e - i )];
		*this += value;
	}
	Bignum& operator<<=( int n )
	{
		assert( n <= 64 );
		// complement of number of bits to be shifted
		const int nc = 64 - n;
		// holds interchunk carry
		unsigned long long carry = 0u;
		for( auto& chunk : bits )
		{
			unsigned long long newCarry = chunk >> nc;
			if( n < 64 )
			{
				chunk = (chunk << n) | carry;
			}
			else
			{
				chunk = carry;
			}
			carry = newCarry;
		}
		// carry out from highest chunk means add new chunk!
		if( carry != 0u )
		{
			bits.push_back( carry );
		}
		return *this;
	}
	Bignum& operator>>=( int n )
	{
		assert( n <= 64 );
		// complement of number of bits to be shifted
		const int nc = 64 - n;
		// holds interchunk carry
		unsigned long long carry = 0u;
		for( auto i = bits.rbegin(),e = bits.rend();
				i != e; i++ )
		{
			const unsigned long long newCarry = *i << nc;
			if( n < 64 ) // @@@ missed this case
			{
				*i = (*i >> n) | carry;
			}
			else
			{
				*i = carry;
			}
			carry = newCarry; // @@@forgot this
		}
		// remove top chunk if now zero
		if( bits.back() == 0u )
		{
			bits.pop_back();
		}
		return *this;
	}
	Bignum operator<<( int n ) const
	{
		return Bignum( *this ) <<= n;
	}
	Bignum operator >> ( int n ) const
	{
		return Bignum( *this ) >>= n;
	}
	Bignum& operator+=( const Bignum& rhs )
	{
		// reallocate lhs size to be at least same as rhs
		if( bits.size() < rhs.bits.size() )
		{
			bits.resize( rhs.bits.size() );
		}
		// problems here!!!!! @@@@@ rhs smaller carry out carry propages how handle??
		unsigned long long carry = 0u;
		size_t i = 0u;
		{
			const size_t end = rhs.bits.size();
			for( ; i < end; i++ )
			{
				// keep old value to test for overflow later
				const auto old = bits[i];
				bits[i] = old + rhs.bits[i] + carry;
				// if old greater than new, must have overflown so set carry
				if( old > bits[i] )
				{
					carry = 1u;
				}
				else
				{
					carry = 0u;
				}
			}
		}
		// propagate final carry
		const size_t end = bits.size();
		for( ; carry != 0u && i < end; i++ )
		{
			// keep old value to test for overflow later
			const auto old = bits[i];
			bits[i] = old + carry;
			// if old greater than new, must have overflown so set carry
			if( old > bits[i] )
			{
				carry = 1u;
			}
			else
			{
				carry = 0u;
			}
		}
		// if there was a carry out of the last position
		// add one more chunk up top with val 1
		if( carry != 0u )
		{
			bits.push_back( 1u );
		}
		return *this;
	}
	Bignum operator+( const Bignum& rhs ) const
	{
		return Bignum( *this ) += rhs;
	}
	Bignum& operator+=( unsigned long long rhs )
	{
		if( bits.size() == 0u )
		{
			bits.push_back( rhs );
		}
		else
		{
			const auto prev = bits.front();
			bits.front() += rhs;
			unsigned long long carry = 0u;
			if( prev > bits.front() )
			{
				carry = 1u;
			}
			// keep adding while there is a carry
			for( size_t i = 1,end = bits.size(); carry != 0u && i < end; i++ )
			{
				const auto prev = bits[i];
				bits[i] += carry;
				if( prev <= bits[i] )
				{
					carry = 0u;
				}
			}
			// if still carry, push one back
			if( carry != 0u )
			{
				bits.push_back( 1u );
			}
		}
		return *this;
	}
	Bignum operator+( unsigned long long rhs ) const
	{
		return Bignum( *this ) += rhs;
	}
	Bignum& operator-=( unsigned long long rhs )
	{
		assert( bits.size() > 0u );

		const auto prev = bits.front();
		bits.front() -= rhs;
		unsigned long long borrow = 0u;
		if( prev < bits.front() )
		{
			borrow = 1u;
		}
		// keep adding while there is a carry
		for( size_t i = 1,end = bits.size(); borrow != 0u && i < end; i++ )
		{
			const auto prev = bits[i];
			bits[i] -= borrow;
			if( prev >= bits[i] )
			{
				borrow = 0u;
			}
		}
		// check if we can shrink
		if( bits.back() == 0u )
		{
			bits.pop_back();
		}
		return *this;
	}
	Bignum operator-( unsigned long long rhs ) const
	{
		return Bignum( *this ) -= rhs;
	}
	Bignum& operator*=( unsigned long long rhs )
	{
		if( !IsZero() )
		{
			size_t size = bits.size();
			const size_t original_size = size;

			// start at high digit
			// first multiply usually pushes new chunk
			{
				// multiply (h:high result l:low result)
				unsigned long long h;
				const unsigned long long l = _mulx_u64( bits[size - 1],rhs,&h );

				// set position value
				bits[size - 1] = l;

				// push high if > 0
				if( h != 0u )
				{
					bits.push_back( h );
					size++;
				}
			}

			// start from second chunk
			for( size_t i = original_size - 2; i < original_size; i-- )
			{
				// multiply (h:high result l:low result)
				unsigned long long h;
				const unsigned long long l = _mulx_u64( bits[i],rhs,&h );

				// set position value
				bits[i] = l;

				// add high
				unsigned char c = _addcarry_u64( 0u,bits[i + 1],h,&bits[i + 1] );
				// propagate carry (until final place)
				for( size_t j = i + 2; c != 0u && j < size; j++ )
				{
					c = _addcarry_u64( c,bits[j],0u,&bits[j] );
				}
				// push new chunk if carry out of last chunk
				if( c != 0u )
				{
					bits.push_back( 1u );
					size++;
				}
			}
		}
		return *this;
	}
	Bignum operator*( unsigned long long rhs ) const
	{
		return Bignum( *this ) *= rhs;
	}
	Bignum& operator++()
	{
		return *this += 1u;
	}
	Bignum& operator--()
	{
		return *this -= 1u;
	}
	unsigned long long ToInteger() const
	{
		return bits.front();
	}
	bool IsOne() const
	{
		return bits.size() == 1u && bits.front() == 1u;
	}
	bool IsZero() const
	{
		return bits.size() == 0u;
	}
	const auto& GetBits() const
	{
		return bits;
	}
	size_t GetChunkCount() const
	{
		return bits.size();
	}
	unsigned long long GetLow() const
	{
		return bits.size() > 0u ? bits.front() : 0u;
	}
	void SetLow( unsigned long long lo )
	{
		assert( bits.size() > 0u );
		bits.front() = lo;
	}
	// counts number of trailing zeros in low chunk (up to 64)
	int CountLowZeroes() const
	{
		// empty number has no trailing zeros
		const auto size = bits.size();
		if( size == 0u )
		{
			return 0;
		}
		auto number = GetLow();
		// all zeros, return 64 (maximum trailing zeroes detected)
		if( number == 0u )
		{
			return 64;
		}
		// otherwise count trailing zeros
		int c = 0;
		for( ; (number & 1u) == 0u && number != 0u; c++,number >>= 1 );
		return c;
	}
private:
	std::vector<unsigned long long> bits;
	static constexpr unsigned long long pow[20] = {
		1,
		10,
		100,
		1000,
		10000,
		100000,
		1000000,
		10000000,
		100000000,
		1000000000,
		10000000000,
		100000000000,
		1000000000000,
		10000000000000,
		100000000000000,
		1000000000000000,
		10000000000000000,
		100000000000000000,
		1000000000000000000,
		10000000000000000000
	};
};

// 8-bit lookup table (fits in L1, fast to generate)
// contains the # of steps needed to shift right by 5
// need to take into account carry out!! and state of low 3 bits
// add that info to the LUT
template<int bitcount>
class LUT
{
public:
	struct Entry
	{
		Entry( char steps,char lostate )
			:
			steps( steps ),
			lostate( lostate )
		{}
		unsigned char steps;
		unsigned char lostate;
	};
public:
	// generate the LUT
	LUT()
	{
		entries.reserve( GetLUTSize() );
		for( unsigned long long bits = 0ull; bits < GetLUTSize(); bits++ )
		{
			auto bits_temp = bits;
			unsigned char count = 0u;
			for( int shift = 0; shift < GetShiftAmount(); count++ )
			{
				if( (bits_temp & 0b1ull) == 0ull )
				{
					// shift right
					bits_temp >>= 1ull;
					shift++;
				}
				else
				{
					// if 4 lsb are
					// 1011
					// 0111 or
					// 1111
					// it is worth it to add (can stack up a row of ones or knock a row down)
					if( (bits_temp & 0b10ull) != 0ull && (bits_temp & 0b1100ull) != 0ull )
					{
						++bits_temp;
					}
					else
					{
						// otherwise subtracting is just as good or better
						--bits_temp;
					}
				}
			}
			entries.emplace_back( count,unsigned char( bits_temp ) );
		}
	}
	// perform lookup
	const Entry& operator[]( unsigned long long bits ) const
	{
		return entries[bits & mask];
	}
	static constexpr int GetSignificantBitsRequired()
	{
		return bitcount;
	}
	static constexpr int GetShiftAmount()
	{
		return bitcount - 3;
	}
	static constexpr size_t GetLUTSize()
	{
		return size_t( mask + 1ull );
	}
private:
	static constexpr unsigned long long mask = (0b1ull << bitcount) - 1ull;
	std::vector<Entry> entries;
};

std::ostream& operator<<( std::ostream& lhs,const Bignum& rhs )
{
	auto copy = rhs;
	std::string bit_string;
	for( ; !copy.IsZero(); copy >>= 1 )
	{
		bit_string.push_back( (copy.GetLow() & 0b1) ? '1' : '0' );
	}
	std::reverse( bit_string.begin(),bit_string.end() );
	lhs << bit_string;
	return lhs;
}

int main()
{
	FrameTimer ft;

	std::string digits;
	std::ifstream( "number.txt" ) >> digits;

	ft.Mark();
	Bignum bits = digits;
	float t1 = ft.Mark();

	// generate lookup table (11 or 12 bits seems to be the balance for 6900 digits)
	LUT<12> lut;
	float tl = ft.Mark();

	int count = 0;
	// perform lookup while more than N significant bits
	for( unsigned long long lobits = bits.GetLow();
			bits.GetChunkCount() > 1u || lobits >= lut.GetLUTSize(); lobits = bits.GetLow() )
	{
		const auto& entry = lut[lobits];
		count += entry.steps;
		// perform shift
		bits >>= lut.GetShiftAmount();
		// fix low 3 bits
		bits.SetLow( (bits.GetLow() & ~0b111ull) | (entry.lostate & 0b111ull) );
		// add in 4th (carry) bit
		bits += unsigned long long( entry.lostate & 0b1000u );
	}
	// handle remaining N bits with simple algorithm
	while( !bits.IsOne() )
	{
		const int trailingZeroes = bits.CountLowZeroes();
		if( trailingZeroes > 0 )
		{
			// shift right while even
			bits >>= trailingZeroes;
			count += trailingZeroes;
		}
		else
		{
			// if 4 lsb are
			// 1011
			// 0111 or
			// 1111
			// it is worth it to add (can stack up a row of ones or knock a row down)
			const auto low = bits.GetLow();
			if( (low & 0b10) != 0u && (low & 0b1100) != 0u )
			{
				++bits;
				count++;
			}
			else
			{
				// otherwise subtracting is just as good or better
				--bits;
				count++;
			}
		}
	}

	float t2 = ft.Mark();

	std::cout << count << " " << t1 << " " << tl << " " << t2 << std::endl;
	std::cout << "Total time: " << t1 + tl + t2;
	std::cin.get();
	return 0;
}