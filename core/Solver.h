#ifndef zmaxsat_Solver_h

#define zmaxsat_Solver_h
#include "../mtl/Vec.h"
#include "../mtl/Heap.h"
#include "../mtl/Alg.h"
#include "../core/SolverTypes.h"
#include "../core/debug.h"

namespace zmaxsat{

class Solver{
public:
        Solver();
        virtual ~Solver();
        // Constructor/Destructor
        Var newVar (bool sign = true,bool dvar=true);
        void setDecisionVar(Var v,bool b);
        void insertVarOrder(Var x);

        lbool value(Var x) const{return varAssigns[x].current; }
        lbool value(Lit p)  const{ return (varAssigns[var(p)].current) ^(sign(p)) ;}
        CRef reason(Var x)const{return vardata[x].reason;}
        int      level            (Var x) const {return vardata[x].dl;}
        int state(Var x) const{vardata[x].vstate;}

        void setnVars(uint32_t n){nVars=n;}
        void setnClauses(uint32_t n){ nClauses=n;}
        void setisWeight(uint32_t n){ isWeight=n;}
        void setHardWeight(uint32_t n){ hardWeight=n;}
        void setPartial(uint32_t n){ partial=n;}

        uint32_t getHardWeight() const {return hardWeight;}
        uint32_t getisWeight() const {return isWeight;}
        uint32_t getpartial() const{return partial;}
        uint32_t getnVars() const {return nVars;}
        uint32_t getnClauses() const {return nClauses;}
        uint32_t getUB() const {return UB;}
        uint32_t getoriginalClauseN() const {return originalClauseN;}
        uint32_t getBranchNode()const {return BranchNode;}
        uint32_t getNbBack() const {return NbBack;}
        uint32_t getconflictNumber() const {return conflictNumber;}

        bool     locked           (const Clause& c) const;
        int    nvars()const {return vardata.size();}
        void      dpl();
        uint32_t verifySolution();
        int pickBranchLit();//choose a decision variable
        #if DEBUG_CLAUSE
            CRef addClause( vec<Lit>& ps);
        #else
            bool addClause( vec<Lit>& ps);
        #endif // DEBUG_CLAUSE
        void addliteralIndex( CRef cr);//add literal (in clause) into literal_in
        void attachClause(CRef cr);//attach clause into watches
        void detachClause(CRef cr,bool strict=false);//detach clause from watches
        void removeclause(CRef cr);//remove clause/delete clause

	void  removeSatisfiedClause(Lit literal);//according to the literal_in ,then push the satisfied clauses into stack(passiveClause)
	int  reduceClauses(Lit literal );//according to watches,simplify the clauses
        void PASSIVElsetofOriClause(CRef cr);//set the learntset of original clause PASSIVE;

	int  lookAhead();//yu gu
	void  removeCSets(CRef cr);//push the conflictclause set of learntClause into passiveClause
	int  lookAheadUP(uint32_t Conflicts);
	CRef propagate(int starting);//my_unitclause process
	int analyze(CRef confl, vec<Lit>& out_learnt,vec<CRef>& set);//analyze conflict clause
	CRef satisfyUnitClause(CRef cl);//satisfy the clause in myunitclause stack
        CRef myPropagate(Lit lit);//my_reduce_clauses();old function
        void storeLearntClause(vec<Lit>& learnt);//add learnt clause and it's conflict set to ca; create_learnt_clause( ) old
	int  addLearntClauseIndex(CRef cr);//add all index; watches literal in,original clause' learnt set
	int  storeInferenceGraph(CRef clause);//find all inference graph ;store_csets_of_learntc(clause) old ;
        int  resetContext(int clausePoint, int trailPoint,int unitClausePoint);
        int  removeInferenceGraph(vec<CRef>& conflictset);//store the set into passiveClause;remove_clauses_csets()old
        int  setpassive_Leantc_of_Iclause(int start);

        int  backtracking(  );

        void varBumpActivity(Var v, double inc);
        void varBumpActivity(Var v);
        void varDecayActivity();
        void claDecayActivity();
        void claBumpActivity (Clause& c);

        bool simplify(Lit p);
        bool solve();

        void cancelConflictSet();

        void processUnitClause();

        inline int decisionLevel(){return currentDl;}
        uint32_t abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
        bool litRedundant(Lit p, uint32_t abstract_levels);

        #if DEBUG_SOLVER
        void debugMain()
        {
            CRef test;
            vec<Lit> &tmp=createVecLit(5,-1,2,3,-4,5);
            test=addClause(tmp);
            Clause &cla=ca[test];
            cla.showclause(true);

        }
        #endif

protected:
        struct VarData { int vstate;CRef reason; int dl; };
        static inline VarData mkVarData(int state,CRef reason, int dl){VarData d={state,reason,dl};return d;}

        struct VarValue {lbool current;lbool rest;};
        static inline VarValue mkVarValue(lbool current, lbool rest){VarValue v={current,rest};return v;}

	struct SavedVar{int passiveCpoint;int zeroCpoint;int nbEmptyPoint;int unitCpoint;};
	static inline SavedVar mkSavedVar(int pc,int zc,int ne,int uc){ SavedVar s={pc,zc,ne,uc};return s;}



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

        struct ClauseDeleted{
                const ClauseAllocator& ca;
                ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
                bool operator()(const CRef& cr ) const { return ca[cr].mark() == 1; }
        };

        OccLists<Lit, vec<Watcher>, WatcherDeleted> watches;
        OccLists<Lit,vec<CRef>, ClauseDeleted> literal_in;

        struct VarOrderLt {
                const vec<double>&  activity;
                bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
                VarOrderLt(const vec<double>&  act) : activity(act) { }
        };

        uint32_t nVars,nClauses,originalClauseN,BranchNode,NbBranch;
        uint32_t LB,UB,NbBack,conflictNumber,priorConfsets;//backing number;valid conflict analyz number;store learnt clause's set
        uint32_t hardWeight,isWeight,partial,NbEmpty;
        unsigned long int learntsLiterals,clausesLiterals;
        double maxlearnts,totliterals;
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
        vec<CRef> unitClause;
	vec<CRef> zeroClause;

        vec<CRef> conflictClauseSet;//store learnt clause's conflict clause set;conSet_of_learnc old
        vec<Lit> tempLearntClause;//store learnt clause by analyze
        vec<CRef> inferenceClauseSet;//store all clauses in inferencegraph
        vec<int> polarity;
        //about variable

        vec<VarValue> varAssigns;
        vec<VarData> vardata;
        vec<lbool> varBestValue;
        vec<double> varActivity;
        vec<int> seen;
        vec<Lit> trail;
        Heap<VarOrderLt> orderHeap;
        vec<Var> branchVars;//saved the branch var
        vec<Lit> anaylzeStack;
        vec<Lit> analyzeToclear;
        vec<bool> decision;//show if a var is a decision var
        //int decVars;
        uint64_t dec_vars;
        int ccmin_mode;

};

inline void     Solver::setDecisionVar(Var v, bool b)
{
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}

inline void Solver::insertVarOrder(Var x) {
    if (!orderHeap.inHeap(x) && decision[x]) orderHeap.insert(x); }


inline bool     Solver::locked          (const Clause& c) const {
         return (value(c[0]) == l_True) && (reason(var(c[0])) != CRef_Undef) &&( ca.lea(reason(var(c[0]))) == &c);
 }

}
#endif

