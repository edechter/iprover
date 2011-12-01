#ifndef MINIMAL_CORE_H
#define MINIMAL_CORE_H

#include "simp/SimpSolver.h"
#include "mtl/Map.h"

namespace Minisat 
{

class CMinimalCore
{
public:
    CMinimalCore(SimpSolver& solver);

    void SetUidToIcs(uint32_t nClsUid, uint32_t nIc);

    lbool Solve(bool pre);

    inline SimpSolver& GetSolver() { return m_Solver; }

    void SetICNum(uint32_t nIcNum);

    bool m_bIcInConfl;
private:
   void PrintData(int unknownSize, int mucSize, int iter, bool last = false);

   uint32_t GetMaxIc(Map<uint32_t, uint32_t>& mapIcToScore);
   uint32_t GetMinIc(Map<uint32_t, uint32_t>& mapIcToScore);

    vec<uint32_t> m_UidToIC;
    vec<vec<uint32_t> > m_IcToUids;
    SimpSolver& m_Solver;
    uint32_t m_nICSize;
};

}

#endif
