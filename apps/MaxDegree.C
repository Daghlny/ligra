
// author: yn

#include "ligra.h"

template<typename vertex>
struct MAXDEG_F {
    vertex *V;
    uintE maxdeg;
    MAXDEG_F(vertex *_V):V(_V), maxdeg(0){}

    /* PUSH SPARSE */ /* DENSE_FORWARD */
    inline bool update(uintE s, uintE d){
        if (V[s].getInDegree() > maxdeg)
            maxdeg = V[s].getInDegree();
        return false;
    }

    /* PULL DENSE */
    inline bool updateAtomic(uintE s, uintE d){
        if (V[s].getInDegree() > maxdeg)
            maxdeg = V[s].getInDegree();
        return false;
    }

    inline bool cond (uintE d) {
        //cout << "cond(" << d << ");" << endl;
        return true;
    }
};

template <class vertex>
void Compute(graph<vertex>& GA, commandLine P) {
    long n = GA.n;
    uintE *indices = new uintE[n];
    for (int i = 0; i < n; ++i) indices[i] = i;
    vertexSubset Frontier(n, n, indices);
    
    MAXDEG_F<vertex> mf(GA.V);
    while(!Frontier.isEmpty()){
        vertexSubset output = edgeMap(GA, Frontier, mf);
        Frontier.del();
        Frontier = output;
    }

    cout << "Max Degree: " << mf.maxdeg << endl;
}

