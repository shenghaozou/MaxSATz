#include <math.h>
#include "../mtl/Sort.h"
#include "../core/Solver.h"
using namespace zmaxsat;
/*specification:
  Input:
  OutPut:
  Function:init the solver
*/
Solver::Solver():hardWeight(0),partial(0),

    //Parameters
    watches(WatcherDeleted(ca)),
    literal_in(ClauseDeleted(ca)),
    orderHeap(VarOrderLt(varActivity))
    {}

Solver::~Solver()
{}
/*specification:
  Input: variable sign and variable ID
  OutPut:
  Function: init  variable memory room and property when read input file
*/
Var Solver::newVar (bool sign,bool dvar ){
    int v = nvars();
    watches.init(mkLit(v, false));
    watches.init(mkLit(v, true ));
    //add literal_in===================================
    literal_in.init(mkLit(v, false));
    literal_in.init(mkLit(v, true ));
    varAssigns.push(mkVarValue(l_Undef,l_Undef ) );
    vardata.push(mkVarData(ACTIVE,CRef_Undef, 0));
    varActivity .push(0);
    //varActivity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
    }
/*specification:
  Input:
  OutPut:
  Function: control the maxsat whole process and find the solution if solution exists,varBestValue store the solution
*/
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
	       if(trail.size()==0)  break;
        }
        if(pickBranchLit()==NONE)
                while(backtracking()==NONE) ;

    }while(trail.size()>0);

}

/*specification:
  Input:
  OutPut: nb means the number of unsatisfed clause of CNF under a group complete assignments
  Function: check whether the nbempty is equal with the real unsatisfed clause of CNF under a group complete assignments
*/
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

/*specification:
  Input:
  OutPut: NONE means LB>=UB; TRUE means LB<UB and continue to estimate LB with lookahead function
  Function:choose the branch variable, change the branch variable's property and saved breakpoint information for backtracking
*/
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
                //branchVars.push(next);
                vardata[next]=mkVarData(PASSIVE,CRef_Undef,++NbBranch);
                trail.push(literal);

                currentDl=NbBranch;

                if(reduceClauses(literal) == NONE)
                        return NONE;
                removeSatisfiedClause(literal);
                return TRUE;
	}

#if DEBUG_CLAUSE
    CRef Solver::addClause( vec<Lit>& ps)
    {
            assert(currentDl==0);

            sort(ps);
            Lit p;
            int i,j;
            for(i=j=0,p=lit_Undef;i<ps.size();i++){
                    if((value(ps[i] )==l_True)||(ps[i]==~p)){
                            nClauses--;return CRef_Undef;
                    }

                    else if(value(ps[i])!=l_False && ps[i]!=p)
                            ps[j++]=p=ps[i];
            }
            ps.shrink(i-j);
            assert(ps.size()!=0);
//当ps为单子句时，如何存储，blocker里面为何值？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？
            CRef cr=ca.alloc(ps);
            clauses.push(cr);
            addliteralIndex(cr);
            attachClause(cr);

            if(ps.size()==2)
            {
                    varActivity[var(ps[0])]++;
                    varActivity[var(ps[1])]++;
            }
            else if(ps.size()==1)
                    unitClause.push(cr);
            return cr;
    }
#else
/*specification:
  Input: Lit vector
  OutPut:
  Function:store clause to ca and add index to literal index and watcher list when read input file. unit clause's block is NONE which is -1; push unit clause into unitClause
*/
    bool Solver::addClause( vec<Lit>& ps){
            assert(currentDl==0);
            if(ps.size()==0) return TRUE;
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
#endif // DEBUG_CLAUSE

/*specification:
  Input:clause's cref
  OutPut:
  Function: add clause to literal_in when reading input file or creating new learnt clause
*/
void Solver::addliteralIndex(CRef cr){//add cref into literal_in
	        const Clause&c=ca[cr];
	        assert(c.size()>0);
	        for(int i=0;i<c.size();i++)
                        literal_in[c[i]].push(cr);

        }
/*specification:
  Input: clause's cref
  OutPut:
  Function: add clause to watcher list when reading input file or creating new learnt clause;unit clause block is NONE which is -1
*/
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
/*specification:
  Input:clause's cref, strict'default value is false
  OutPut:
  Function: remove clauses(marked deleted) from watch list and literal_in;
*/
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

/*specification:
  Input: clause's cref
  OutPut:
  Function: remove clause from ca when
*/
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
/*specification:
  Input: literal is branch lit
  OutPut:
  Function: removed satisfied clause when simply cnf according to branch lit;clause's cref is pushed into passiveClause
*/
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
/*specification:
  Input: original clause's cref
  OutPut:
  Function: push clause cref in passiveClause; those clauses are learnt clauses; state form active to passive;when simply cnf or estimation
*/
        void Solver::PASSIVElsetofOriClause(CRef cr){
                Clause& c=ca[cr];
                vec<CRef>* lset=c.lSetHeader();
                for(int i=0;i<lset->size();i++){
                        Clause & c=ca[(*lset)[i]];
                        if( c.state() !=PASSIVE){
                                 c.state(PASSIVE);
                                passiveClause.push((*lset)[i]);
                        }
                }

        }
/*specification:
  Input: branch lit
  OutPut:
  Function: simply cnf with branch literal; if clause is unit clause, NbEmpty++;if clauses are learn clause and become empty, state is zero;
  if clauses are original clause and become empty, state is passive,NbEmpty++,call PASSIVElsetofOriClause ;
  set unit clause's decision level
*/
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
                                else{
                                        // 单子菊的层次?????????????????????????????????????????
                                        unitClause.push(cr);
                                        c.dl(currentDl);
                                }

                                NextClause: ;
                        }
                        else*j++=*i++;
                }
                ws.shrink(i-j);
                return TRUE;
        }//according to watches,simplify the clauses

/*specification:
  Input: learnt clause's cref
  OutPut:
  Function: push learnt clause's conflict set in passiveClause when learnt clause become passive
  移除的时候，子句的状态必须是active，否则回溯就会有问题
*/
	void  Solver::removeCSets(CRef cr){
	        //移除冲突集的时候是不是 冲突集里的自句的状态必定都是ACTIVE？，否则就是中间有问题
	        Clause& lclause=ca[cr];
	        for(int i=0;i<lclause.cSetSize();i++){
                        CRef c=lclause.cSet(i);
                        Clause& cla=ca[cr];
                        //if(cla.state()==ACTIVE)
                                passiveClause.push(c);
                                cla.state(PASSIVE);
	        }

        }//push the conflictclause set of learntClause into passiveClause
/*specification:
  Input:
  OutPut:if return NONE, LB>=UB; if return conflict, LB<=UB
  Function:begin to estimate;first process zero learnt clause; then call lookaheadUP;resetcontext the solver

  在预估的时候，一定要注意状态的还原。lookahead函数的resetcontext函数需要把solver的状态还原到调用之前，这里面包括unitClause，
*/
    int  Solver::lookAhead(){
            int savedpassiveClause,savedunitClause,savedvar;
            savedpassiveClause=passiveClause.size();
            savedunitClause=unitClause.size();
            savedvar=trail.size();

            uint32_t conflict=0;
//对zero栈的处理放在设置保存断电前还是后，为什么？？？？？？？？？？？？？？？
            for(int position=0;position<zeroClause.size();position++){
                CRef cr=zeroClause[position];
                Clause& c=ca[cr];
                if(c.state()==ZERO){
                        conflict++;
                        if(conflict+NbEmpty>=UB) return NONE;
                        c.state(PASSIVE);
                        passiveClause.push(cr);
                        removeCSets(cr);}
            }

            conflict=lookAheadUP(conflict);
            if(conflict+NbEmpty>=UB) return NONE;
            else {
//resetcontext的作用，以及reset再什么时候进行？？？？？？？？？？？？？？？？？？？？？
                  //resetContext();
                return conflict;
            }

        }//yu gu
/*specification:
  Input:
  OutPut:
  Function:
*/
	int  Solver::lookAheadUP(uint32_t Conflicts){
                int savedpassiveClause,savedunitClause,savedvar;
                savedpassiveClause=passiveClause.size();
                savedunitClause=unitClause.size();
                savedvar=trail.size();
                CRef clause;
                int starting= savedVariable[var(trail[savedvar-1] ) ].unitCpoint;

                while(( clause=propagate( starting))  !=CRef_Undef ){
                        if(analyze(clause,tempLearntClause,conflictClauseSet)!=FALSE){
                                storeLearntClause(tempLearntClause);
                        }
                        storeInferenceGraph(clause);
                        removeInferenceGraph(inferenceClauseSet);

                        Conflicts++;
                        if(Conflicts+NbEmpty>=UB) return NONE;
                }
                //vec.shrink(i)这个函数是否可以来代替resetcontext
                resetContext(savedpassiveClause,savedvar,savedunitClause);
                return Conflicts;
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
CRef Solver::propagate(int starting){
                for(int position=starting;position<unitClause.size();position++){
                        CRef unitclause=unitClause[position];
                        Clause &c=ca[unitclause];
                        if(c.state()==ACTIVE){
                                myUnitClause.clear();
                                if(CRef cr=(satisfyUnitClause(unitclause) )!=CRef_Undef)
                                        return cr;
                                else{
                                        for(int myposition=0;myposition<myUnitClause.size();myposition++){
                                                CRef myunitclause=myUnitClause[myposition];
                                                Clause& myc=ca[myunitclause];
                                                if(myc.state()==ACTIVE)
                                                        if(CRef mycr=(satisfyUnitClause(myunitclause) )!=CRef_Undef)
                                                                return mycr;
                                        }//end for myUnitClause
                                }
                        }//end active unitclause
                }//end for unitClause
        }//unitclause process
/*specification:
  Input:
  OutPut:
  Function:
*/
        bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
        {
                anaylzeStack.clear(); anaylzeStack.push(p);
                int top = analyzeToclear.size();
                while (anaylzeStack.size() > 0){
                        assert(reason(var(anaylzeStack.last())) != CRef_Undef);
                        Clause& c = ca[reason(var(anaylzeStack.last()))]; anaylzeStack.pop();

                        for (int i = 1; i < c.size(); i++){
                                Lit p  = c[i];
                                if (!seen[var(p)] && level(var(p)) > 0){
                                        if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                                                seen[var(p)] = 1;
                                                anaylzeStack.push(p);
                                                analyzeToclear.push(p);
                                        }else{
                                                for (int j = top; j < analyzeToclear.size(); j++)
                                                seen[var(analyzeToclear[j])] = 0;
                                        analyzeToclear.shrink(analyzeToclear.size() - top);
                                        return false;}
                                }
                        }//end for
                }//end while

                return true;
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
	int Solver::analyze(CRef confl, vec<Lit>& out_learnt,vec<CRef>& cset){
	        int pathC = 0;
                Lit p     = lit_Undef;

                out_learnt.push();      // (leave room for the asserting literal)
                int index   = trail.size() - 1;

                do{
                        assert(confl != CRef_Undef); // (otherwise should be UIP)
                        Clause& c = ca[confl];
                        if (c.learnt())
                        claBumpActivity(c);

                        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
                                Lit q = c[j];
                                if (!seen[var(q)] && level(var(q)) > 0){
                                        varBumpActivity(var(q));
                                        seen[var(q)] = 1;
                                        if (level(var(q)) >= decisionLevel())
                                                pathC++;
                                        else
                                                out_learnt.push(q);
                                }
                        }//end for
                        cset.push(confl);
                // Select next clause to look at:
                        while (!seen[var(trail[index--])]);
                        p     = trail[index+1];
                        confl = reason(var(p));
                        seen[var(p)] = 0;
                        pathC--;
                }while (pathC > 0);
                out_learnt[0] = ~p;

                // Simplify conflict clause:
                int i, j;
                out_learnt.copyTo(analyzeToclear);
                if (ccmin_mode == 2){
                        uint32_t abstract_level = 0;
                        for (i = 1; i < out_learnt.size(); i++)
                        abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

                        for (i = j = 1; i < out_learnt.size(); i++)
                        if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                                out_learnt[j++] = out_learnt[i];
                }else if (ccmin_mode == 1){
                        for (i = j = 1; i < out_learnt.size(); i++){
                                Var x = var(out_learnt[i]);

                                if (reason(x) == CRef_Undef)
                                        out_learnt[j++] = out_learnt[i];
                                else{
                                        Clause& c = ca[reason(var(out_learnt[i]))];
                                        for (int k = 1; k < c.size(); k++)
                                        if (!seen[var(c[k])] && level(var(c[k])) > 0){
                                                out_learnt[j++] = out_learnt[i];
                                                break; }
                                }
                        }//end for
                }else
                        i = j = out_learnt.size();
                maxlearnts += out_learnt.size();
                out_learnt.shrink(i - j);
                totliterals += out_learnt.size();

                for (int j = 0; j < analyzeToclear.size(); j++)
                        seen[var(analyzeToclear[j])] = 0;    // ('seen[]' is now cleared)
        }//analyze conflict clause
/*specification:
  Input:
  OutPut:
  Function:
*/
	CRef Solver::satisfyUnitClause(CRef cr){
                Clause& c=ca[cr];
                Lit literal=c[0];
                bool sig=sign(literal);
                //需要判断这个子句的第一个文字是否为ACTIVE吗？？？？？？？？？？？？？？？？？
                trail.push(literal);
                c.state(PASSIVE);
                passiveClause.push(cr);
                vardata.push(mkVarData(PASSIVE, cr, c.dl() ) );
                varAssigns.push(mkVarValue( lbool( (uint8_t)sig), l_Undef));//??????????????????????????

                CRef con=myPropagate(literal) ;
                return con;

        }//satisfy the clause in myunitclause stack
/*specification:
  Input:
  OutPut:
  Function:
*/
        CRef Solver::myPropagate(Lit lit){
                vec<Watcher>& ws=watches[lit];
                Watcher* i,*j,*end;
                for(i=j=(Watcher*)ws,end=i+ws.size();i!=end;){
                        Lit blocker=i->blocker;
                        CRef cr=i->cref;
                        Clause& c=ca[cr];
                        if(c.state()==ACTIVE){
                                //当cr为单子句时，如何存储，blocker里面为何值,要判断是不是原始的单子ju为FALSE？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？？
                                if(blocker==lit_Undef){
                                        while(i!=end )         *j++=*i++;
                                        ws.shrink(i-j);
                                        return cr;
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
                                        while(i!=end )         *j++=*i++;
                                        ws.shrink(i-j);
                                        return cr;
                                }
                                else{
                                        // 单子菊的层次?????????????????????????????????????????
                                        myUnitClause.push(cr);
                                        c.dl(vardata[var(lit) ].dl );
                                }
                                NextClause: ;
                        }
                        else
                                *j++=*i++;
                }
                ws.shrink(i-j);
                return CRef_Undef;
        }//my_reduce_clauses();old function
/*specification:
  Input:
  OutPut:
  Function:
*/
        void Solver::storeLearntClause(vec<Lit>& learnt){
                 //假设冲突集再这里面被替换
                 for(int i=0;i<conflictClauseSet.size();i++){
                        CRef cr=conflictClauseSet[i];
                        Clause& c=ca[cr];
                        if(!c.learnt()){
                                c.involved(1);
                        }
                        else{//冲突集里面有学习子句
                                remove(conflictClauseSet,cr);
                                for(int i=0;i<c.cSetSize();i++){//替换
                                        CRef conf=c.cSet(i);
                                        Clause& cc=ca[conf];
                                        if(cc.involved() ) continue;
                                        else {
                                                cc.involved(1);
                                                conflictClauseSet.push(conf);  }
                                }
                        }
                 }
                CRef cr=ca.alloc(learnt,true,conflictClauseSet);
                learnts.push(cr);
                addLearntClauseIndex(cr);
                //如果学习子句为单子句要加入单子句栈 吗？？？？？？？？？？

        }//add learnt clause and it's conflict set to ca; create_learnt_clause( ) old
/*specification:
  Input:
  OutPut:
  Function:
*/
	int  Solver::addLearntClauseIndex(CRef cr){
                attachClause(cr);
                addliteralIndex(cr);
                for(int i=0;i<conflictClauseSet.size();i++){
                        CRef cr=conflictClauseSet[i];
                        Clause& c=ca[cr];
                        vec<CRef>* lset=c.lSetHeader();
                        lset->push(cr);
                }

        }//add all index; watches literal in,original clause' learnt set
/*specification:
  Input:
  OutPut:
  Function:
*/
	int  Solver::storeInferenceGraph(CRef clause){
                assert(false);
        }//find all inference graph ;store_csets_of_learntc(clause) old ;
/*specification:
  Input:
  OutPut:
  Function:
*/
        int  Solver::resetContext(int clausePoint, int trailPoint,int unitClausePoint){
                assert(false);
        }

/*specification:
  Input:
  OutPut:
  Function:
*/        int  Solver::removeInferenceGraph(vec<CRef>& conflictset){
                for(int i=0;i<conflictset.size();i++){
                        CRef cr=inferenceClauseSet[i];
                        passiveClause.push(cr);
                        Clause& c=ca[cr];
                        c.state(PASSIVE);
                }
        }//store the set into passiveClause;remove_clauses_csets()old
/*specification:
  Input:
  OutPut:
  Function:
*/
        int  Solver::setpassive_Leantc_of_Iclause(int start){
                assert(false);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        int  Solver::backtracking(  ){
                assert(false);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        void Solver::varDecayActivity(){
                varInc *= (1 / varDecay);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, varInc); }
/*specification:
  Input:
  OutPut:
  Function:
*/
        inline void Solver::varBumpActivity(Var v, double inc) {
                if ( (varActivity[v] += inc) > 1e100 ) {
        // Rescale:
                for (int i = 0; i < getnVars(); i++)
                        varActivity[i] *= 1e-100;
                varInc *= 1e-100; }

    // Update order_heap with respect to new activity:
                if (orderHeap.inHeap(v))
                        orderHeap.decrease(v);
        }

/*specification:
  Input:
  OutPut:
  Function:
*/
        void Solver::claDecayActivity(){
                clauseInc *= (1 / clauseDecay);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        void Solver::claBumpActivity (Clause& c) {
                if ( (c.activity() += clauseInc) > 1e20 ) {
            // Rescale:
                for (int i = 0; i < learnts.size(); i++)
                        ca[learnts[i]].activity() *= 1e-20;
                clauseInc *= 1e-20; }
             }
/*specification:
  Input:
  OutPut:
  Function:
*/
        bool Solver::simplify(Lit p){
                assert(false);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        bool Solver::solve(){
                assert(false);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/

        void Solver::cancelConflictSet(){
                assert(false);
        }
/*specification:
  Input:
  OutPut:
  Function:
*/
        void Solver::processUnitClause(){
                assert(false);
        }
