#include <math.h>
#include "../mtl/Sort.h"
#include "../core/Solver.h"
using namespace zmaxsat;

Solver::Solver():
    //Parameters
    watches(WatcherDeleted(ca)),
    literal_in(ClauseDeleted(ca)),
    orderHeap(VarOrderLt(varActivity))
    {}

Solver::~Solver()
{}

Var Solver::newVar (bool sign,bool dvar ){
        int v = nvars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    //add literal_in===================================
    literal_in  .init(mkLit(v, false));
    literal_in  .init(mkLit(v, true ));
    varAssigns  .push(mkVarValue(l_Undef,l_Undef ) );
    vardata  .push(mkVarData(ACTIVE,CRef_Undef, 0));
    varActivity .push(0);
    //varActivity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
    }

void Solver::dpl()
{
    uint32_t conflict;
    int i;
    do{
        if(trail.size()==nVars){
                UB=NbEmpty;
                conflict=verifySolution( );//get real number of empty clauses
                if(conflict != NbEmpty )
                        printf("ERROR: Solution verification fails, real_empty = %u, NbEmpty = %u.\n",conflict, NbEmpty);
	       printf("o %u\n",UB);
	       for(int i=0;i<nVars;i++){
                        varBestValue[i]=varAssigns[i].current;
	       }
	       while(backtracking()==NONE);
	       if(trail.size()==0)         break;
        }
        if(pickBranchLit()==NONE)
                while(backtracking()==NONE) ;

    }while(trail.size()>0);

}

        uint32_t Solver::verifySolution( ){//get real number of empty clauses
                int i,j,clause_truth;
                CRef cr;

                uint32_t nb=0;

                for( i =0 ; i< originalClauseN ; i++){
                        clause_truth = FALSE;
                        cr = clauses[i];
                        Clause& c=ca[cr];
                        for(j=0 ; j <c.size() ;j++){
                                if(value(c[j]) == l_True){
                                        clause_truth = TRUE;
                                        break;
                                }
                                if(clause_truth==FALSE)
                                        nb++;
                        }
                }
                return nb;
        }

	int Solver::pickBranchLit(){//choose a decision variable
	        Var next=var_Undef;
	        BranchNode++;
	        if(lookAhead()==NONE)
                        return NONE;//LB>=UB
                if(orderHeap.empty()){
                        next=var_Undef;

                }
                else
                        next=orderHeap.removeMin();

                if (next==var_Undef) return FALSE;

                savedVariable[next]=mkSavedVar(passiveClause.size(), zeroClause.size(), NbEmpty,unitClause.size() ) ;
                varAssigns[next]=mkVarValue(l_False,l_True);
                if(vardata[next].vstate==PASSIVE)
                        printf("ERROR: Assigning passive variable.\n");
                Lit literal=mkLit(next,false);
                vardata[next]=mkVarData(PASSIVE,CRef_Undef,++NbBranch);
                trail.push(literal);

                currentDl=NbBranch;

                if(reduceClauses(literal) == NONE)
                        return NONE;
                removeSatisfiedClause(literal);
                return TRUE;
	}

    bool Solver::addClause( vec<Lit>& ps){
            assert(currentDl==0);

            sort(ps);
            Lit p;
            int i,j;
            for(i=j=0,p=lit_Undef;i<ps.size();i++){
                    if((value(ps[i] )==l_True)||(ps[i]==~p)){
                            nClauses--;return TRUE;
                    }

                    else if(value(ps[i])!=l_False && ps[i]!=p)
                            ps[j++]=p=ps[i];
            }
            ps.shrink(i-j);
//当ps为单子句时，如何存储，blocker里面为何值？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？
            CRef cr=ca.alloc(ps);
            clauses.push(cr);
            addliteralIndex(cr);
            attachClause(cr);

            if(ps.size()==2){
                    varActivity[var(ps[0])]++;
                    varActivity[var(ps[1])]++;
            }
            else if(ps.size()==1)
                    unitClause.push(cr);
                    else if(ps.size()==0)
                            return FALSE;
            return TRUE;
    }

	void Solver::addliteralIndex(CRef cr){//add into literal_in
	        const Clause&c=ca[cr];
	        assert(c.size()>0);
	        for(int i=0;i<c.size();i++)
                        literal_in[c[i]].push(cr);

        }
        void Solver::attachClause(CRef cr){
                const Clause&c=ca[cr];
	        assert(c.size()>0);
//当cr为单子句时，如何存储，blocker里面为何值？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？
                if(c.size()==1){
                        watches[~c[0]].push(Watcher(cr,lit_Undef));
                }
	        watches[~c[0]].push(Watcher(cr,c[1]));
	        watches[~c[1]].push(Watcher(cr,c[0]));
	        if(c.learnt()) learntsLiterals+=c.size();
	        else
                        clausesLiterals+=c.size();
        }

        void Solver::detachClause(CRef cr,bool strict){
                const Clause& c = ca[cr];
                assert(c.size() > 1);
                if (strict){
                        remove(watches[~c[0]], Watcher(cr, c[1]));
                        remove(watches[~c[1]], Watcher(cr, c[0]));
                        remove(literal_in[c[0]],cr);
                        remove(literal_in[c[1]],cr);
                }
                else{
                        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
                        watches.smudge(~c[0]);
                        watches.smudge(~c[1]);
                        literal_in.smudge(c[0]);
                        literal_in.smudge(c[1]);
                }
                if (c.learnt()) learntsLiterals -= c.size();
                else            clausesLiterals -= c.size();
        }

        void Solver::removeclause(CRef cr){ //remove clause/delete clause
                Clause & c=ca[cr];
                detachClause(cr);

                if(c.learnt()){
                        for(int i=0;i<c.cSetSize();i++){
                                CRef cr=c.cSet(i);
                                vec<CRef>& lset=*(c.lSetHeader());
                                remove(lset,cr);
                        }
                }

                if( locked(c))
                        vardata[var(c[0])].reason=CRef_Undef;
                c.mark(1);
                ca.free(cr);
        }

	void  Solver::removeSatisfiedClause(Lit literal){//according to the literal_in ,then push the satisfied clauses into stack(passiveClause)
                vec<CRef>& litvec=literal_in[literal];
                for(int i=0;i<litvec.size();i++){
                        Clause & c=ca[litvec[i]];
                        if( (c.state() )==ACTIVE){
                                c.state(PASSIVE);
                                passiveClause.push(litvec[i]);
                        }
                }
        }

        void Solver::PASSIVElsetofOriClause(CRef cr){
                Clause& c=ca[cr];
                vec<CRef>* lset=c.lSetHeader();
                for(int i=0;i<lset->size();i++){
                        Clause & c=ca[(*lset)[i]];
                        if( c.state() !=FALSE){
                                 c.state(PASSIVE);
                                passiveClause.push((*lset)[i]);
                        }
                }

        }

	int  Solver::reduceClauses(Lit literal ){
                vec<Watcher>& ws=watches[literal];
                Watcher* i,*j,*end;
                for(i=j=(Watcher*)ws,end=i+ws.size();i!=end;){
                        Lit blocker=i->blocker;
                        CRef cr=i->cref;
                        Clause& c=ca[cr];
                        if(c.state()==ACTIVE){
                                //当cr为单子句时，如何存储，blocker里面为何值,要判断是不是原始的单子ju为FALSE？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？
                                if(blocker==lit_Undef){
                                        if(!c.learnt()){//originalclause become FALSE
                                                NbEmpty++;
                                                if(NbEmpty>UB)
                                                        while(i<end) {*j++=*i++; return NONE;}
                                                c.state(PASSIVE);
                                                passiveClause.push(cr);
                                                PASSIVElsetofOriClause(cr);
                                        }
                                        else{//learntclause become FALSE
                                                c.state(ZERO);
                                                zeroClause.push(cr);
                                        }
                                        *j++=*i++;continue;
                                }

                                Lit false_lit=~blocker;
                                if(c[0]==false_lit){ c[0]=c[1];c[1]=false_lit;}
                                assert(c[1]==false_lit);
                                i++;

                                Lit first=c[0];
                                Watcher w=Watcher(cr,first);
                                if (first != blocker && value(first) == l_True){
                                        *j++ = w; continue; }

                                for(int k=2;k<c.size();k++){
                                        if(value(c[k] ) != l_False){
                                                c[1]=c[k];c[k]=false_lit;
                                                watches[~c[1]].push(w);
                                                goto NextClause;  }
                                }

                                *j++ = w ;
                                if(value(first) == l_False){
                                        if(!c.learnt()){//originalclause become FALSE
                                                NbEmpty++;
                                                if(NbEmpty>UB){
                                                        while(i<end) {*j++=*i++; return NONE;}
                                                }
                                                c.state(PASSIVE);
                                                passiveClause.push(cr);
                                                PASSIVElsetofOriClause(cr);
                                        }
                                        else{//learntclause become FALSE
                                                c.state(ZERO);
                                                zeroClause.push(cr);
                                        }
                                }
                                else//becom unitclause
                                        unitClause.push(cr);
                                NextClause: ;
                        }
                }
                ws.shrink(i-j);
                return TRUE;
        }//according to watches,simplify the clauses



	void  Solver::removeCSets(CRef cr){
	        Clause& lclause=ca[cr];
	        for(int i=0;i<lclause.cSetSize();i++){
                        CRef c=lclause.cSet(i);
                        Clause& cla=ca[cr];
                        if(cla.state()==ACTIVE)
                                passiveClause.push(c);
	        }

        }//push the conflictclause set of learntClause into passiveClause

    int  Solver::lookAhead(){
                assert(false);
        }//yu gu
	int  Solver::lookAheadUP(uint32_t Conflicts){
                assert(false);
        }
	CRef Solver::propagate(int starting){
                assert(false);
        }//unitclause process

	void Solver::analyze(CRef confl, vec<Lit>& out_learnt,vec<CRef>& set){
                assert(false);
        }//analyze conflict clause

	CRef Solver::satisfyUnitClause(CRef cl){
                assert(false);
        }//satisfy the clause in myunitclause stack

        CRef Solver::myPropagate(Lit lit){
                assert(false);
        }//my_reduce_clauses();old function

        void Solver::storeLearntClause(vec<Lit>& learnt){
                assert(false);
        }//add learnt clause and it's conflict set to ca; create_learnt_clause( ) old

	int  Solver::addLearntClauseIndex(){
                assert(false);
        }//add all index; watches literal in,original clause' learnt set

	int  Solver::storeInferenceGraph(CRef clause){
                assert(false);
        }//find all inference graph ;store_csets_of_learntc(clause) old ;

        int  Solver::resetContext(int clausePoint, int trailPoint,int unitClausePoint){
                assert(false);
        }
        int  Solver::removeInferenceGraph(vec<CRef>& conflictset){
                assert(false);
        }//store the set into passiveClause;remove_clauses_csets()old

        int  Solver::setpassive_Leantc_of_Iclause(int start){
                assert(false);
        }

        int  Solver::backtracking(  ){
                assert(false);
        }

        void Solver::varDecayActivity(){
                assert(false);
        }
        void Solver::claDecayActivity(){
                assert(false);
        }

        bool Solver::simplify(Lit p){
                assert(false);
        }
        bool Solver::solve(){
                assert(false);
        }


        void Solver::cancelConflictSet(){
                assert(false);
        }

        void Solver::processUnitClause(){
                assert(false);
        }
