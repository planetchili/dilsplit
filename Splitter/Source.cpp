#include <vector>
#include <string>
#include <cassert>
#include <algorithm>
#include <iostream>
#include "FrameTimer.h"

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
		Bignum scratch;
		scratch.bits.reserve( estimated_bits / 64 + 1 );
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
			MulPow10( 19,scratch );
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
		MulPow10( int( e - i ),scratch );
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
	Bignum operator>>( int n ) const
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
	void MulPow10( int power,Bignum& scratch = Bignum{} )
	{
		const auto& seq = shiftTable[power - 1];
		*this <<= seq.front();
		scratch = *this;
		for( auto i = seq.cbegin() + 1,e = seq.cend(); i != e; i++ )
		{
			scratch <<= *i;
			*this += scratch;
		}
	}
private:
	std::vector<unsigned long long> bits;
	static std::vector<std::vector<int>> shiftTable;
};

std::vector<std::vector<int>> Bignum::shiftTable = {
	{ 1,2 },
	{ 2,3,1 },
	{ 3,2,1,1,1,1 },
	{ 4,4,1,1,3 },
	{ 5,2,2,1,5,1 },
	{ 6,3,5,2,1,1,1 },
	{ 7,2,1,2,3,4,1,3 },
	{ 8,5,1,1,1,2,2,1,1,1,1,2 },
	{ 9,2,3,1,2,2,1,3,1,1,2,1,1 },
	{ 10,3,1,1,1,1,2,7,2,2,3 },
	{ 11,2,1,1,2,1,2,1,1,5,3,2,1,1,2 },
	{ 12,4,2,3,2,3,2,2,1,4,2,1,1 },
	{ 13,2,2,3,1,1,3,1,1,3,5,1,4,3 },
	{ 14,3,2,1,1,1,6,4,1,3,1,1,1,2,2,1,2 },
	{ 15,2,1,4,1,3,3,2,2,1,1,1,1,1,2,2,1,4,1,1 },
	{ 16,6,1,1,1,1,1,2,1,3,3,1,1,1,2,1,5,1,1,4 },
	{ 17,2,4,1,2,1,1,2,5,1,1,1,2,2,4,2,1,4,1,2 },
	{ 18,3,1,2,1,1,3,2,1,1,3,1,2,2,1,2,1,2,6,1,1,1,2,1 },
	{ 19,2,1,1,1,3,4,3,6,1,4,3,1,1,4,1,2,2,4 },
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

	Bignum bits = "125343425741238979834759095074898208959032487921897123874843128794387934298723498732489720323489723478978249372849378429372809427480924738974389789049807242437892748932784932489702437892437892437892473892789042874392487398249732879433780423879234879248739243879789203728904287493287904248973890742234789287493243879243879248739782493278439724839278349728940782094274830247389243789247389243789789240274839427389247389728493284739243879248730780924728093789024870924274839789042098173890799823740981237941234980238904890713809789712347890123897409812749801237479802873498273048970231907487129480712398471238947123084701239874219387478902478213890478970218947231890741978047890123798042429387123498142398128907892734809714809714980714978012987012987031908714908721987021390714290821498012439841239812438912348912349821493891842021438989127412897398071298071298071298071298701498071298071298071298071298071298071270312874908127489123789471293847123804721398479832179471293749812379401237890472307498012749801274123984718904980127489127908471238470812739840172149012742120934712394718207487123908123743129047123934871238094712749081274908123741239074123094817490812741025017234981273498123747812984071092378012498132980401238479801480712830470127480129874980234789013784123078479801274012741283749081237487180237432190740918742874934875908234789523789053747095";

	int count = 0;
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

	std::cout << count << " " << ft.Mark();
	std::cin.get();
	return 0;
}