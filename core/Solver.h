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

	uint32_t getUB(){return UB;}
	uint32_t getHardWeight(){return HardWeight;}
	uint32_t getnvar(){return nvar;}
	uint32_t getnclauses(){return nclauses;}
	
	bool dpl();
	int pickBranchLit();//choose a decision variable
	
    void addClause(const vec<Lit>& ps);
	void addliteralIndex(int cn,CRef cr);//add into literal_in
    void attachClause(CRef cr);
    void detachClause(CRef cr,bool strict);
    void removeClause(CRef cr);// judge the clause satisfied or not
	int  removeSatisfiedClause(Lit literal);//according to the literal ,then push the satisfied clauses into stack(passiveClause)
	int  reduceClauses(Lit literal );//according to the literal,simplify the clauses
	
	int  lookAhead();//yu gu 
	int  removeCSets(CRef cr);//push the conflictclause set of learntClause into passiveClause
	int  lookAheadUP(uint32_t Conflicts);
	CRef propagate(int starting);//unitclause process
	void analyze(CRef confl, vec<Lit>& out_learnt,vec<CRef>& set);//analyze conflict clause
	CRef satisfyUnitClause(CRef cl);//satisfy the clause in myunitclause stack
    CRef myPropagate(Lit lit);//my_reduce_clauses();old function
    void storeLearntClause(vec<Lit>& learnt);//add learnt clause and it's conflict set to ca; create_learnt_clause( ) old
	int  addLearntClauseIndex();//add all index; watches literal in,original clause' learnt set
	int  storeInferenceGraph(CRef clause);//find all inference graph ;store_csets_of_learntc(clause) old ;
    int  resetContext(int clausePoint, int trailPoint,int unitClausePoint);
    int  removeInferenceGraph(vec<CRef>& conflictset);//store the set into passiveClause;remove_clauses_csets()old
    int  setpassive_Leantc_of_Iclause(int start);
	
    int  backtracking(  );
	
    void varDecayActivity();
    void claDecayActivity();

    bool simplify(Lit p);
    bool solve();
    
    
    void cancelConflictSet();

    void processUnitClause();

    inline int decisionLevel(){return currentDl;}




protected:
    struct VarData { int vstate;CRef reason; int dl; };
    static inline VarData mkVarData(int state,CRef reason, int dl){VarData d={state,reason,dl};return d;}
    struct VarValue {int current;int rest;};
    static inline VarValue mkVarValue(int current, int rest){VarValue v={current,rest};return v;}
    
	struct SavedVar{int passiveCpoint;int zeroCpoint;int nbEmptyPoint;int unitCpoint;};



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
	double varInc,varDecay,clauseInc,clauseDecay;
	
    ClauseAllocator ca;	
	
    vec<CRef> clauses; //cn/cref转换
	vec<CRef> learnts;
    
    vec<double> clauseActivity;
	vec<SavedVar> savedVariable;//saved interrupt at branchnode
	
    vec<CRef> passiveClause;
    vec<CRef> myUnitClause;//used in lookAhead()
    vec<CRef> unitclause;
	vec<CRef> zeroClause;
	
    vec<CRef> learntClauseSet;//store learnt clause's conflict clause set;conSet_of_learnc old
    vec<CRef> tempLearntClause;//store learnt clause by analyze
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

