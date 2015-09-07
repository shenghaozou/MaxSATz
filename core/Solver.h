#ifndef zmaxsat_Solver_h

#define zmaxsat_Solver_h
#include "../mtl/Vec.h"
#include "../mtl/Heap.h"
#include "../mtl/Alg.h"
#include "../core/SolverTypes.h"

namespace zmaxsat
{

class Solver
{
public:
    Solver();
    virtual ~Solver();
    // Constructor/Destructor
    Var newVar (bool polarity = true);

    bool addClause(const vec<Lit>& ps);
    void attachClause(CRef cr);
    void detachClause(CRef cr,bool strict);
    void removeClause(CRef cr);

    void varDecayActivity();
    void claDecayActivity();

    bool simplify(Lit p);
    bool solve();
    bool dpl();
    void lookahead();
    void cancelConflictSet();

    void processUnitClause();

    Lit pickBranchLit();




protected:
    struct VarData { int vstate;CRef reason; int dl; };
    static inline VarData mkVarData(int state,CRef reason, int dl){VarData d={state,reason,dl};return d;}
    struct VarValue {int current;int rest;};
    static inline VarValue mkVarValue(int current, int rest){VarValue v={current,rest};return v;}
    inline int decisionLevel(){return currentDl;}

    ClauseAllocator ca;

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    OccLists<Lit, vec<Watcher>, WatcherDeleted> watches;
    LitLists<Lit,vec<CRef> > literal_in;

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
    VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    uint32_t nvar,nclauses,originalClauseN,BRANCH_NODE,NB_BRANCHE;
    uint32_t LB,UB,NB_BACK,conflictNumber,priorConfsets;//backing number;valid conflict analyz number;store learnt clause's set
    uint32_t isWeight,partial,NB_EMPTY;
    unsigned long int learntsLiterals;
    double maxlearnts;
    double learntsize_adjust_confl;
    int learntsize_adjust_cnt;
    int currentDl;
    vec<CRef> clauses; //cn/cref转换
    double varInc,varDecay,clauseInc,clauseDecay;

    vec<double> clauseActivity;

    vec<CRef> passiveClause;
    vec<CRef> myUnitClause;
    vec<CRef> unitclause;
    vec<CRef> learntClause;
    vec<CRef> reasonStack;
    vec<CRef> tempLearntClause;
    vec<int> polarity;
    //about variable

    vec<VarValue> varAssigns;
    vec<VarData> vardata;
    vec<lbool> varBestValue;
    vec<double> varActivity;
    vec<int> seen;
    vec<int> trail;
    Heap<VarOrderLt> orderHeap;
    vec<Var> branchVars;
    vec<Lit> anaylzeStack;
    vec<bool> decision;//show if a var is a decision var
    int decVars;

};

}
#endif

