
#include "ligrabitMatrix.hpp"

#include <sys/time.h>
#include <assert.h>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <cstring>
#include <cstdint>
#include <cmath>
#include <cstddef>
#include <bitset>
#include <string>
#include <iostream>
#include <map>
#include <vector>
#include <list>
#include <utility>
#include <algorithm>

using std::cout;
using std::endl;
using std::bitset;
using std::string;
using std::hex;

static uint32_t masks_32bits[32] = {
    0x80000000,0x40000000,0x20000000,0x10000000,
    0x08000000,0x04000000,0x02000000,0x01000000,
    0x00800000,0x00400000,0x00200000,0x00100000,
    0x00080000,0x00040000,0x00020000,0x00010000,
    0x00008000,0x00004000,0x00002000,0x00001000,
    0x00000800,0x00000400,0x00000200,0x00000100,
    0x00000080,0x00000040,0x00000020,0x00000010,
    0x00000008,0x00000004,0x00000002,0x00000001,
};

static uint32_t front_32bits[32] = {
    0x8fffffff,0x4fffffff,0x2fffffff,0x1fffffff,
    0x08ffffff,0x04ffffff,0x02ffffff,0x01ffffff,
    0x008fffff,0x004fffff,0x002fffff,0x001fffff,
    0x0008ffff,0x0004ffff,0x0002ffff,0x0001ffff,
    0x00008fff,0x00004fff,0x00002fff,0x00001fff,
    0x000008ff,0x000004ff,0x000002ff,0x000001ff,
    0x0000008f,0x0000004f,0x0000002f,0x0000001f,
    0x00000008,0x00000004,0x00000002,0x00000001,
};

static uint8_t masks_8bits[8] = {
    0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01
};

bitVector::bitVector():
    head(nullptr), num(0)
{
    //this is for vector initalization
}

bitVector::bitVector(elem_t *_h, size_t _n):
    head(_h), num(_n)
{
    //nothing to do 
}

bitVector::bitVector(elem_t *_h, size_t _n, size_t _valid_bit_num):
    head(_h), num(_n), valid_bit_num(_valid_bit_num)
{
    //nothing to do
}

void
bitVector::reset(elem_t *_h, size_t _n, size_t _valid)
{
    head = _h;
    num  = _n;
    valid_bit_num = _valid;
}

/** \brief set all bit in bitVector to the given bitvalue
 *  \param flag the given value("0" or "1")
 */
void
bitVector::setall(int flag)
{
    //elem_t eflag = flag == 0 ? ALLZERO : ALLONE;
    uint8_t bitflag = flag == 0 ? 0x00 : 0xff;
    memset(head, bitflag, sizeof(elem_t) * num);
    /*
    for (size_t i = 0; i < num; ++i)
        head[i] = eflag;
        */
}

/** \brief set the given index corresponding bit as given value. /
 *         If the ind is beyond the range of valid index, then it will return -1.
 *  \param ind the index of required bit
 *  \param flag the bit value
 */
int
bitVector::setbit(int ind, int flag)
{
    //if ( ind > EBIT * num - 1 )
    if ((size_t)ind > valid_bit_num - 1 || ind < 0)
    {
        LOG("invalid @ind value (%d)\n", ind);
        return -1;
    }
    uint32_t *convert_ptr = (uint32_t*)head;
    int offset = ind % 32;
    int cnt = ind / 32;
    if (flag == 0)
    {
        uint64_t mask = ~masks_32bits[offset];
        convert_ptr[cnt] &= mask;
    } else 
    {
        convert_ptr[cnt] |= masks_32bits[offset];
    }
    return 0;
}

/** \brief set the front partition marked by lend to the given flag
 *  \param lend the last out-of-range index, it means [0, lend)
 *  \param flag given flag, "0" or "1"
 */
int
bitVector::setfront(int lend, int flag)
{
    if ( lend < 0 || (size_t)lend > valid_bit_num ){
        LOG("lend(%d) is out of valid range[0, %lu)\n", lend, valid_bit_num);
        return -1;
    }
    int frontnum = lend / EBIT;
    int offset = lend % EBIT;
    for ( int cnt = 0; cnt < frontnum; ++cnt )
    {
        if ( flag == 0 ){
            head[cnt] = 0x00;
        } else {
            head[cnt] = ALLONE;
        }
    }
    if ( offset != 0 )
    {
        if ( flag == 0 )
        {
            elem_t mask = ALLONE >> offset;
            head[frontnum] = head[frontnum] & mask;
        } else {
            elem_t mask = ALLONE << (EBIT - offset);
            head[frontnum] = head[frontnum] | mask;
        }
    }
    return 0;
}

/** \brief  check whether the bitVector is all "1" or "0" decided by the @flag
 *  \param flag the given flag, any value not equals to "0" is treated as "1".
 */
bool
bitVector::all(int flag)
{
    if (flag == 0)
    {
        for ( size_t i = 0; i < num; ++i )
            if ( head[i] > 0 ) return false;
        return true;
    } else {
        for (size_t i = 0; i < num; ++i)
            if (head[i] == 0) return false;
        return true;
    }
    return true;
}

// get the first of bit which is @flag
int 
bitVector::first(int flag)
{
    uint32_t *convert_ptr = (uint32_t*)head;
    double e32_num = (EBIT / 32) * num;
    if (flag == 0)
    {
        // search for first of "0"
        // This branch is not optimized, because it is not used in BMBK
        for (size_t i = 0; i < num; ++i)
        {
            if ( head[i] == ALLONE ) continue;
            for ( int bit = 0; bit < EBIT; ++bit )
            {
                if ( ((elem_t)(head[i] >> (EBIT-bit-1)) & (0x01)) == 0 )
                {
                    size_t res = i * EBIT + bit;
                    if ( res < valid_bit_num )
                        return res;
                    else
                        return -1;
                }
            }
        }
    } else
    {
        for (size_t i = 0; i < e32_num; ++i){
            if ( convert_ptr[i] == ALLZERO) continue;
            int bit = 0;
            while(bit < 32 && convert_ptr[i] < masks_32bits[bit])
                ++bit;
            size_t res = i * 32 + bit;
            return (res < valid_bit_num) ? res : -1;
        }
    }
    return -1;
}

/** \brief the last index of bit which is flag
 *  \param flag the given bit value
 */
int 
bitVector::last(int flag)
{
    if (flag == 0)
    {
        // search for the last of "0"
        for (int i = num-1; i >= 0; --i)
        {
            if (head[i] == ALLONE) continue;
            for (int bit = EBIT-1; bit >= 0; --bit)
            {
                if ( ((elem_t)(head[i] >> (EBIT-bit-1)) & (0x01)) == 0)
                {
                    size_t res = i * EBIT + bit;
                    if ( res < valid_bit_num )
                        return res;
                    else
                        continue;
                }
            }
        }
    } else
    {
        // search for the last of "1"
        for (int i = num-1; i >= 0; --i)
        {
            if (head[i] == ALLZERO) continue;
            for (int bit = EBIT-1; bit >= 0; --bit)
            {
                if ( ((elem_t)(head[i] >> (EBIT-bit-1)) & (0x01)) != 0)
                {
                    size_t res = i * EBIT + bit;
                    if ( res < valid_bit_num )
                        return res;
                    else
                        continue;
                }
            }
        }
    }
    return -1;
}


/** \brief get all indices of "1" in bitVector, this function is used
 *  for get maximal clique vertices in Pmat
 *  \param inds the return indices reference
 */
int
bitVector::allone(list<int> &inds)
{
    int id = 0;
    int count = 0;
    //Warning: Pay Attention to Little-Endian feature
    //uint8_t *convert_ptr = (uint8_t*)(head);
    int offset = valid_bit_num % EBIT;
    int valid_elem_num = valid_bit_num / EBIT;
    //int valid_byte_num = valid_bit_num / 8;
    //Warning: These codes indicate the program only can run with 32bits
    int cnt = 0;
    for (; cnt < valid_elem_num; ++cnt)
    {
        if (head[cnt] == 0)
            continue;
        for (int off = 0; off < EBIT; ++off)
            if ((head[cnt] & masks_32bits[off]) != 0 )
            {
                inds.push_back(cnt*EBIT + off);
                ++count;
            }
    }
    for (int off = 0; off < offset ; ++off)
        if ((head[cnt] & masks_32bits[off]) != 0)
        {
            inds.push_back(cnt*EBIT + off);
            ++count;
        }

    return count;
}

/** \brief get the number of "1" in bitVector
 */
int
bitVector::allone()
{
    /* Warning: This function maybe wrong with Little-Endian feature */
    int count = 0;
    //uint8_t *convert_ptr = static_cast<uint8_t*>(head);
    uint8_t *convert_ptr = (uint8_t *)(head);
    int valid_byte_num = valid_bit_num / 8;
    int offset = valid_bit_num % 8;
    unsigned int c = 0;
    for ( int cnt = 0; cnt < valid_byte_num; ++cnt )
    {
        uint8_t n = convert_ptr[cnt];
        for ( c=0; n; ++c )
            n &= n-1;
        count += c;
    }
    for (int cnt = 0; cnt < offset; ++cnt)
    {
        if ( (convert_ptr[valid_byte_num] >> (7-cnt)) & 0x01 != 0)
            ++count;
    }
    return count;
}

/** \brief set the last "1" in bitVector to "0" with a fast method
 */
int
bitVector::setlastone()
{
    for ( int i = num-1; i >= 0; --i )
    {
        if (head[i] == ALLZERO) continue;
        head[i] = head[i] & (head[i]-1);
        break;
    }
    return -1;
}

/** \brief return the ind bit in bitVector's value("0" or "1")
 *  \param ind the required bit index in bitVector
 */
bool
bitVector::operator[] (const size_t ind) const
{
    //assert( ind < EBIT*num );
    assert(ind < valid_bit_num);
    int offset = ind % (EBIT);
    int cnt = ind / EBIT;
    elem_t mask = 0x01 << (EBIT - offset - 1);
    return (bool)(head[cnt] & mask);
}

/** \brief set the value of bitVector as two bitVector's AND operation result. /
 *         You can think it as a intersect operation
 *  \param lhs the first bitVector operand
 *  \param rhs the second bitVector operand
 */
int
bitVector::setWithBitAnd(bitVector &lhs, bitVector &rhs)
{
    if (lhs.num != rhs.num )
        return -1;
    for ( size_t i = 0; i < rhs.num; ++i )
        head[i] = lhs.head[i] & rhs.head[i];
    return 0;
}

/** \brief set the value of bitVector as two bitVector's OR operation result
 *  \param lhs the first bitVector operand
 *  \param rhs the second bitVector operand
 */
int
bitVector::setWithBitOR(bitVector &lhs, bitVector &rhs)
{
    if (lhs.num != rhs.num )
        return -1;
    for (size_t i = 0; i < rhs.num; ++i)
        head[i] = lhs.head[i] | rhs.head[i];
    return 0;
}

/** \brief return the binary presentation of bitVector with std::string
 */
string 
bitVector::to_string()
{
    string res = "";
    for ( size_t i = 0; i < num; ++i )
    {
        bitset<EBIT> tmp_bs(head[i]);
        res += (tmp_bs.to_string() + " ");
    }
    return res;
}

/* class localbitVector */

/** \brief the constructor of localbitVector, and assign default value\
 *         as 0
 *  \param _valid_bit_num the desirable bit number of this bitVector
 */
localbitVector::localbitVector(size_t _valid_bit_num):
    bitVector(nullptr, 0, _valid_bit_num), data(nullptr)
{
    if ( valid_bit_num % EBIT )
        num = valid_bit_num / EBIT + 1;
    else 
        num = valid_bit_num / EBIT;
    data = new elem_t[num];
    memset(data, 0, sizeof(elem_t) * num);
    if (data == nullptr){
        LOG("@localbitVector's initialization(@num: %ld) has error\n", num);
        exit(0);
    }

    head = data;
}

localbitVector::~localbitVector()
{
    if ( data != nullptr )
        delete[] data;
}


/* class bitMatrix */

bitMatrix::bitMatrix():
    r_num(0), c_num(0), data(nullptr), rows(0)
{
    //do nothing
}

bitMatrix::bitMatrix(size_t _row, size_t _column):
    r_num(_row), c_num(_column), data(nullptr), rows(_row)
{
    init(_row, _column);
}

bitMatrix::bitMatrix(const bitMatrix &_b):
    r_num(_b.r_num), c_num(_b.c_num), data(nullptr), rows(_b.r_num)
{
    init(r_num, c_num);
}

/** \brief initialize the bitMatrix with given row and column number /
 *         and the values inside the bitMatrix is default assigned 0
 *  \param _row the given row number
 *  \param _column the given column number
 */
void
bitMatrix::init(size_t _row, size_t _column)
{
    r_num = _row;
    c_num = _column;
    rows.resize(_row);

    size_t byte_num_r = ceil((double)(c_num)/8);
    elem_num_r = ceil((double)(byte_num_r)/sizeof(elem_t));
    elem_num = (elem_num_r * r_num);
    data = new elem_t[elem_num];
    assert(data != nullptr);
    /* initialize the @data with 0 */
    memset(data, 0x00, sizeof(elem_t) * elem_num);

    for (size_t i = 0; i < r_num; ++i)
    {
        rows[i] = bitVector(data+i*elem_num_r, elem_num_r, c_num);
    }
}

/** \brief reset the columns and rows of matrix without memory alloc
 *  \param _r new row number
 *  \param _c new column number
 */
int 
bitMatrix::reset(size_t _r, size_t _c)
{
    c_num = _c;
    r_num = _r;
    size_t byte_num_r = ceil((double)(c_num / 8));
    size_t elem_num_r = ceil((double)(byte_num_r) / sizeof(elem_t));

    if (elem_num_r * r_num > elem_num){
        delete[] data;
        data = new elem_t[elem_num_r * r_num];
        if (data == nullptr){
            LOG("@data malloc error\n");
            exit(0);
        }
    }

    elem_num = elem_num_r * r_num;
    //FIX: this operation maybe useless
    memset(data, 0x00, sizeof(elem_t) * elem_num);

    for (size_t i = 0; i < r_num; ++i)
        rows[i].reset(data+i*elem_num_r, elem_num_r, c_num);
}

bitMatrix::~bitMatrix()
{
    delete[] data;
}

/** \brief get the ind row of bitVector
 *  \param ind required row number of matrix
 */
bitVector &
bitMatrix::operator[] (const size_t ind)
{
    if ( ind >= rows.size() )
    {
        LOG("@ind(%lu) is bigger than rows.size()(%lu)\n", ind, rows.size());
        exit(0);
    }
    return rows[ind];
}

/** \brief const version
 *  \param ind required row number of matrix
 */
const bitVector &
bitMatrix::operator[] (const size_t ind) const
{
    if ( ind >= rows.size() )
    {
        LOG("@ind(%lu) is bigger than rows.size()(%lu)\n", ind, rows.size());
        exit(0);
    }
    return rows[ind];
}

/** \brief print bitMatrix row by row
 */
void
bitMatrix::print()
{
    for ( size_t i = 0; i < r_num; ++i)
        cout << rows[i].to_string() << endl;
}

/* Neighborhood */

/** \brief to create a new Neighborhood based on @g and vertex @v
 *  \param g graph structure
 *  \param _v the vertex of Neighborhood
 */
template<class vertex>
Neighborhood<vertex>::Neighborhood(vertex *vers, vid _v):
    bitMatrix(), v(_v)
{
    nbeg = vers[v].getInNeighbors();
    nodenum = vers[v].getInDegree();
    nend = nbeg + nodenum;

    sort(nbeg, nend);
    lower = lower_bound(nbeg, nend, v);
    // begin position of later neighbors 
    laterNbrNum = static_cast<size_t>(nend - lower);
    later = static_cast<size_t>(lower - nbeg);

    if ( lower == nend )
    {
    }
    
    init(laterNbrNum, laterNbrNum);
    assign_rows(vers);
}

template<class vertex> void
Neighborhood<vertex>::Nreset(vertex *vers, vid _v)
{
}

/** \brief assign every row of Neighborhood the intersection between /
 *         the neighbor and vertex @v. The neighbors whose id are smaller /
 *         than @v will only get all "0", because their rows will never used.
 *  \param g graph
 */
template<class vertex> void
Neighborhood<vertex>::assign_rows( vertex *vers )
{
    size_t cnt = 0;
    // @cnt  is the mapped id in Neighborhood
    // @inbr is the index in vertex.nbv
    for ( size_t inbr = later; (vid)inbr < nodenum && cnt < laterNbrNum; ++inbr, cnt++ )
    {
        vid nbr = nbeg[inbr];
        vid *nbrnbv = vers[nbr].getInNeighbors();
        vid nbrdeg  = vers[nbr].getInDegree();

        for (int inbrnbr = 0; inbrnbr < nbrdeg; ++inbrnbr)
        {
            int pos = binary_search(nbrnbv[inbrnbr]);
            pos = pos;
            if ( pos >= 0 )
                rows[cnt].setbit(pos, 1);
        }
        
    }
}

/** \brief use the index in Neighborhood to get the vertex original ID
 *  \param idx the mapped id in @data of Neighborhood
 */
template<class vertex> vid
Neighborhood<vertex>::original_id(int idx)
{
    return lower[idx];
}

template<class vertex> int
Neighborhood<vertex>::mapped_id(vid v)
{
    vid *fpos = std::find(lower, nend, v);
    if ( fpos == nend )
        return -1;
    else
        return static_cast<int>(fpos - lower);
}

/** \brief the total number of neighbors of v
 */
template<class vertex> vid
Neighborhood<vertex>::get_nodenum()
{
    return this->nodenum;
}

template<class vertex> int
Neighborhood<vertex>::binary_search(vid v )
{
    int low = later;
    //int high = static_cast<int>(nend - nbeg);
    int high = nodenum;
    while ( low <= high )
    {
        int mid = (low + high) / 2;
        if ( nbeg[mid] < v )
            low = mid + 1;
        else if ( nbeg[mid] > v )
            high = mid - 1;
        else 
            return mid-later;
    }
    return -1;
}

