
#ifndef LIGRA__BITMATRIX__HPP
#define LIGRA__BITMATRIX__HPP

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
#include "ligra.h"

#define BIT32

#ifdef BIT64
typedef uint64_t elem_t;
#define EBIT 64
#define ALLONE 0xffffffffffffffff
#define ALLZERO 0x0000000000000000
#endif

#ifdef BIT32
typedef uint32_t elem_t;
#define EBIT 32
#define ALLONE 0xffffffff
#define ALLZERO 0x00000000
#endif

#ifdef BIT16
typedef uint16_t elem_t;
#define EBIT 16
#define ALLONE 0xffff
#define ALLZERO 0x0000
#endif

#ifdef BIT8
typedef uint8_t elem_t;
#define EBIT 8
#define ALLONE 0xff
#define ALLZERO 0x00
#endif

#define LOG(fmt, ...) \
    printf("%s | L:%4d | %s() |: " fmt, strrchr(__FILE__, '/')+1, __LINE__, __FUNCTION__, ##__VA_ARGS__)

typedef uintE vid;
using std::vector;
using std::string;
using std::list;


class bitVector
{
    public:
        bitVector();
        bitVector(elem_t *_h, size_t _n);
        bitVector(elem_t *_h, size_t _n, size_t _valid_bit_num);
        
        void reset(elem_t *_h, size_t _n, size_t _valid);
        // set bitVector's bit to @flag
        void setall(int flag);
        int  setbit(int ind, int flag);
        int  setfront(int lend, int flag);
        bool all(int flag);
        int first(int flag);
        int last(int  flag);
        //FIX: implement this method used to select the pivot
        //return all vertices newids which is "1" in bitVector
        int allone(list<int> &inds);
        int allone();
        int setlastone();

        //bool &operator[] (const size_t);
        bool operator[] (const size_t) const;

        // set bitVector's newvalue by AND operation between two other bitVectors
        int setWithBitAnd(bitVector& lhs, bitVector& rhs);
        int setWithBitOR(bitVector& lhs, bitVector &rhs);
        string to_string();

    protected:
        elem_t *head;           // the pointer in corresponding bitMatrix.data
        size_t num;             // number of elem in this bitVector
        size_t valid_bit_num;   // real amount of bits in bitVector
};

class localbitVector: public bitVector
{
    public:
        localbitVector(size_t _valid_bit_num);
        ~localbitVector();

    private:
        elem_t *data;
};

class bitMatrix
{
    public:
        bitMatrix();
        bitMatrix(size_t rownum, size_t columnnum);
        bitMatrix(const bitMatrix& _b);
        void init(size_t rownum, size_t columnnum);
        int  reset(size_t rownum, size_t columnnum);
        ~bitMatrix();

        bitVector &operator[] (const size_t);
        const bitVector &operator[] (const size_t) const;

        virtual void print();

    protected:
        size_t r_num;       // Row number of Matrix
        size_t c_num;       // Column number of Matrix
        size_t elem_num;    // total elem number of Matrix(including all rows)
        size_t elem_num_r;  // elem number of each row

        elem_t *data;
        vector<bitVector> rows;
};

template<class vertex>
class Neighborhood: public bitMatrix
{
    public:
        Neighborhood(vertex *vers, vid v);
        void Nreset( vertex *vers, vid v);
        vid original_id(int idx);
        int mapped_id(vid v);
        vid get_nodenum();

        size_t laterNbrNum;  // number of Later Neighbors

    private:
        void twoAdjlistAND(vid *lower, vid *nb, int index);
        void assign_rows(vertex *vers);
        int  binary_search(vid v);

        vid v;              // v's original ID
        vid *nbeg;          // begin iterator of adjlist
        vid *nend;          // out-of-range end iterator of adjlist
        vid *lower;         // Later Neighbors' begin iter of v
        vid nodenum;        // total number of neighbors of v
        size_t later;       // index of the begin of later neighbors in vertex.nbv
        map<vid, int> dict;
};

#endif

