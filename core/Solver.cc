#include <math.h>
#include "../mtl/Sort.h"
#include "../core/Solver.h"
using namespace zmaxsat;

Solver::Solver():
    //Parameters
    {}

Solver::~Solver()
{}

Var Solver::newVar (bool polarity = true)
{
    assert(false);
}

bool Solver::addClause const vec<Lit>& ps)
{
    assert(false);
}

void Solver::detachClause(CRef cr,bool strict)
{
    assert(false);
}

void Solver::attachClause(CRef cr)
{
    assert(false);
}

void Solver::removeClause(CRef cr)
{
    assert(false);
}

bool Solver::simplify(Lit p)
{
    assert(false);
}

bool Solver::solve()
{
    assert(false);
}

Lit Solver::pickBranchLit()
{
    assert(false);
}

void Solver::processUnitClause()
{
    assert(false);
}

void Solver::varDecayActivity()
{
    assert(false);
}

void Solver::claDecayActivity()
{
    assert(false);
}

uint32_t Solver::lookahead()
{
    assert(false);
}

void lookahead()
{
    assert(false);
}

void cancelConflictSet()
{
    assert(false);
}


bool Solver::dpl()
{
    uint32_t conflict;
    processUnitClause();// push unitclause into the unitClause
    for(;;)
    {
        Lit p=pickBranchLit();
        simplify(p);
        conflict=lookahead();
        if(conflict+NB_EMPTY<UB) cancelConflictSet();
        else backtrack();
    }
}
