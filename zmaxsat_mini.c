/**************************************************************************************************
MaxSAT adopted clause learning based minisat framwork.
**************************************************************************************************/
#include <math.h>
#include <string.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/resource.h>
#include <limits.h>
typedef unsigned int    uint32_t;
typedef unsigned long long int   uint64_t;

#define WORD_LENGTH 1024
#define TRUE 1
#define FALSE 0
#define ACTIVE 1
#define PASSIVE 0
#define NONE -1
#define l_True  0
#define l_False  1
#define l_Undef 2
#define pop(stack)   stack[--stack ## _fill_pointer]
#define push(stack,item)    stack[stack ## _fill_pointer++] = item
#define top(stack)   stack[stack ## _fill_pointer - 1]
#define neglit(p)  p^1
#define parent(i) (i-1)>>1
#define left(i) i*2+1
#define right(i) (i+1)*2
#define ZEROLEN -1
#define NO_CONFLICT -2
#define NO_REASON  -1
#define NEW_LCLAUSE  2
#define learntClen   1024
#define clausesRegion_init_cap  4194304
#define clauses_number_cap  8388608
#define my_clauses_number_cap   1048576
uint64_t HARD_WEIGHT = 0;
uint32_t NB_VAR,NB_CLAUSE,originalClauseN,BRANCH_NODE=0,NB_BRANCHE=0;//
uint32_t LB=0,UB,NB_BACK=0,conflict_number=0,prior_confsets;//backing number;valid conflict analyz number;store learnt clause's set
uint32_t instanceType,partial=0,NB_EMPTY=0;
//activities option
 int   var_inc;       // Amount to bump next variable with.
 int   var_decay;     // INVERSE decay factor for variable activity: stores 1/decay. 
 int   cla_inc;       // Amount to bump next clause with.
 int   cla_decay;     // INVERSE decay factor for clause activity: stores 1/decay.
 uint32_t   maxLearntClause;
struct VarValue{int current; int rest;};
struct VarData { int Vstate; int reason; int level; };
struct Watcher {int cn;  int blocker;}; //clause number and literal
struct VECW {uint32_t  wsize; uint32_t  wcap;  struct Watcher * watchlit;};
struct Clstate{int Cstate;int involved;int weight;};
struct Vec{uint32_t vsize; uint32_t vcap; int* varindex;};
//clauses store and it's property
   int * clausesRegion;
   uint32_t  clausesRegion_size=0;
   uint32_t  clausesRegion_cap;
   uint32_t  clauses_wasted=0; 
   int  clauses_index[clauses_number_cap];       // List of clauses ,store clauses' address in clausesRegion
   int  clauses_index_fill_pointer=0;
   struct Clstate clause_reduce_state[clauses_number_cap]; //claues's reason  dl
   uint32_t clauseActivity[clauses_number_cap];
//reduce clause
   int  clause_stack[clauses_number_cap];                           //store passive clause such as satisfied clause, empty clause ,can not be used learnt clause
   int  clause_stack_fill_pointer=0;
   int  unitclause_stack[my_clauses_number_cap];                        //store unit clause
   int  unitclause_stack_fill_pointer=0;
   int * conSet_of_learnc;   //reason clause reduced learnt clause
   int conSet_of_learnc_fill_pointer=0;
   int conSet_of_learnc_cap;
   int addr_of_learncSet[clauses_number_cap]; //address of learn clause's conflict set 
   int clauseDelete[clauses_number_cap];
   int clauseDelete_fill_pointer=0;
   int clauseDelMark[clauses_number_cap];
   struct Vec * Iclause_index_Lclause;//each clause have learnt clause 
 //  int  Iclause_index_fill_pointer[clauses_number_cap];
   int  my_unit_clause_stack[my_clauses_number_cap];
   int  my_unit_clause_stack_fill_pointer=0;
   int  learntclause[my_clauses_number_cap];
   int  learntclause_fill_pointer=0;
   int* saved_clause_stack;    //store for backtracking
   int* saved_unitclause_stack;
   int* saved_nb_empty;
   int* saved_zeroLclause_stack;
   int  zero_learnt_clause[my_clauses_number_cap]; //parial assignment reduce learnt clause to empty 
   int  zero_learnt_clause_fill_pointer=0;
   int * reason_stack; //store conflict clause in inference graph 
   int  reason_stack_fill_pointer=0;
   int  current_learnt_level;
   int  BCP_variable_index;
   int  temp_learnt_clause[learntClen]; //store new learnt clause
   int  temp_learnt_clause_fill_pointer=0;
   int  DelCount=0;
//watcher list and var index	
   struct VECW * watcherlist;        // two literal watching
   struct Vec * literal_in;  //store the id of clause includes literal,  works as neg_in pos_in in maxsatz
 //variables store and it's property
   int * varCandidate_STACK; //store undefy variable
   int   varCandidate_STACK_fill_pointer=0;
   int * varIndices; //variable index in heap
   uint32_t * varActivity;//variable score  
   struct VarValue * varAssigns;       // Current and rest values of variables.
   int * varBestValue;  // problem solution
   struct VarData * var_reduce_state; //state, reason, decisional level, it is equal to decision vector of MINISAT
   int * seen; 
   int * trail;//store reduced literal
   int  trail_fill_pointer=0;    
   int * dirtyLiteral;
 
int isTrue(int p){return (varAssigns[p>>1].current)^(p&1);}

int pushVetw(struct VECW * wl, int crn, int li){
    struct Watcher * ws; uint32_t  place=wl->wsize;
    if(place==wl->wcap){
        wl->watchlit=(struct Watcher *)realloc(wl->watchlit,(wl->wcap)*2*sizeof(struct Watcher));
        if(wl->watchlit==NULL)  {printf("watchers space assignment erro\n"); return FALSE;}
        wl->wcap*=2;
    }  
    ws=wl->watchlit;
    ws[place].cn=crn;
    ws[place].blocker=li;
    (*wl).wsize++;
}

int popVetw(struct VECW* wl, uint32_t crn, int li){

}

void percolateUP(int i){
  int x=varCandidate_STACK[i];  int p=parent(i);
  while(i!=0&&(varActivity[x]>varActivity[varCandidate_STACK[p]])){
    varCandidate_STACK[i]=varCandidate_STACK[p];
    varIndices[varCandidate_STACK[p]]=i;
    i=p;p=parent(p);
  }
  varCandidate_STACK[i]=x;
  varIndices[x]=i;
}

void percolateDown(int i){
  int child,lvar,rvar,x;
  x=varCandidate_STACK[i];
  while(left(i)<varCandidate_STACK_fill_pointer){
     child=(right(i)<varCandidate_STACK_fill_pointer
	 	&&(varActivity[varCandidate_STACK[right(i)]]>varActivity[varCandidate_STACK[left(i)]]))?right(i):left(i);
     if(varActivity[x]>=varActivity[varCandidate_STACK[child]])
	 break;
     varCandidate_STACK[i]=varCandidate_STACK[child];
     varIndices[varCandidate_STACK[child]]=i;
     i=child;
  }
  varCandidate_STACK[i]=x;
  varIndices[x]=i;
}

void updateVar(int var){
  int i;
  varActivity[var]++;
  if(varActivity[var]>1048576){
    for(i=0;i<NB_VAR;i++)
     varActivity[i]=varActivity[i]/2;
  }
  if(varIndices[var]!=NONE)  //if varialble in heap,update according it's new score
     percolateUP(varIndices[var]);
 //   percolateDown(varIndices[var]);
}

//pick the max score variable from var heap
int removeMax_var(){
   int x=varCandidate_STACK[0]; int var=varCandidate_STACK[varCandidate_STACK_fill_pointer-1];
   varCandidate_STACK[0]=var;
   varIndices[var]=0;
   varIndices[x]=NONE;
   varCandidate_STACK_fill_pointer--;
   if(varCandidate_STACK_fill_pointer>1)
      percolateDown(0);
   return x;
}

//candidate variable insert the heap
void insertVar(int var){  
   varIndices[var]=varCandidate_STACK_fill_pointer;
   push(varCandidate_STACK,var); 
   percolateUP(varIndices[var]);
}
//build two literal watchers
void attachClause(int cn,int cr,int size){
   int * c=&clausesRegion[cr+1];
   if(size==1){  //unit clause 
    pushVetw(&watcherlist[neglit(c[0])], cn,NONE);
    if(unitclause_stack_fill_pointer>=my_clauses_number_cap){printf("unitclause overflow\n"); }
    push(unitclause_stack,cn);
   }
   else{  //add clause to wathers list
      pushVetw(&watcherlist[neglit(c[0])], cn, c[1]);
      pushVetw(&watcherlist[neglit(c[1])], cn, c[0]);
  }
}
//build pos_in ,neg_in for remove satisfied clauses
int attachLiteral(int cn, int * literal,int size){
   int lit,i;   
   for(i=0;i<size;i++){
     lit=literal[i];
     if(literal_in[lit].vsize==0){ 
	literal_in[lit].varindex=(int *)malloc(sizeof(int)*my_clauses_number_cap);
	if(literal_in[lit].varindex==NULL){printf("literal_in malloc error\n"); return FALSE;}
       literal_in[lit].vcap=my_clauses_number_cap;
     }
     if(literal_in[lit].vsize==literal_in[lit].vcap){
	literal_in[lit].varindex=(int *)realloc(literal_in[lit].varindex,sizeof(int)*(literal_in[lit].vcap<<1));
       literal_in[lit].vcap=literal_in[lit].vcap<<1;
       if(literal_in[lit].varindex==NULL) {printf("literal_in realloc error\n");return FALSE;}
     }
     literal_in[lit].varindex[literal_in[lit].vsize++]=cn;
   }
   return TRUE;
}

int initStoreSpace(uint32_t varn,uint32_t clausesn) {
   uint32_t litn,i;
   if(clausesn*2>=clauses_number_cap)
     printf("inputfile clauses number is big\n");
   litn=varn<<1;
   var_reduce_state=(struct VarData *)malloc(varn*sizeof(struct VarData));
   seen=(int *)malloc(varn*sizeof(int));
   varActivity=(uint32_t *)malloc(varn*sizeof(uint32_t));
   varAssigns =(struct VarValue *)malloc(varn*sizeof(struct VarValue));
   varBestValue=(int *)malloc(varn*sizeof(int));
   varIndices=(int *)malloc(varn*sizeof(int));
   trail=(int *)malloc(varn*sizeof(int));
   varCandidate_STACK=(int *)malloc(varn*sizeof(int));
   saved_clause_stack=(int *)malloc(varn*sizeof(int));
   saved_unitclause_stack=(int *)malloc(varn*sizeof(int));
   saved_nb_empty=(int *)malloc(varn*sizeof(int));
   saved_zeroLclause_stack=(int *)malloc(varn*sizeof(int));
   reason_stack=(int *)malloc(varn*sizeof(int));
   dirtyLiteral=(int *)malloc(litn*sizeof(int));
   if(var_reduce_state==NULL||seen==NULL||varActivity==NULL||varAssigns==NULL||saved_unitclause_stack==NULL
   	 ||varIndices==NULL||varCandidate_STACK==NULL||varBestValue==NULL||trail==NULL||saved_clause_stack==NULL
   	 ||saved_nb_empty==NULL||saved_zeroLclause_stack==NULL||dirtyLiteral==NULL)
     return FALSE;
   for(i=0;i<varn;i++)
      varActivity[i]=0;  //should init it here, input file changes the value
  
   for(i=0;i<NB_CLAUSE;i++){  //only score the learnt clauses
     clauseActivity[i]=0; 
   } 
   conSet_of_learnc=(int *)malloc((clausesRegion_init_cap)*sizeof(int));
   if(conSet_of_learnc==NULL) return FALSE;
   conSet_of_learnc_cap=clausesRegion_init_cap;
   clausesRegion=(int *)malloc((clausesRegion_init_cap)*sizeof(int));
   if(clausesRegion==NULL) 
     return FALSE;	
   clausesRegion_cap=clausesRegion_init_cap;
   clausesRegion_size=0;
   watcherlist=(struct VECW*)malloc(litn*sizeof(struct VECW));
   for(i=0;i<litn;i++){
     watcherlist[i].watchlit=(struct Watcher *)malloc(clauses_number_cap*sizeof(struct Watcher));
     watcherlist[i].wsize=0;
     watcherlist[i].wcap=clauses_number_cap;
   }
   Iclause_index_Lclause=(struct Vec*)malloc(clauses_number_cap*sizeof(struct Vec));
   
   literal_in=(struct Vec *)malloc(litn*sizeof(struct Vec));
   for(i=0;i<litn;i++){
     literal_in[i].vsize=0; literal_in[i].vcap=0;
   }
}

void freespace(  ){
  int i;
   if(var_reduce_state!=NULL)
     free(var_reduce_state);
   free(seen);free(varActivity);free(varAssigns);free(varBestValue);free(varIndices);
   free(trail);free(varCandidate_STACK);free(saved_clause_stack);free(saved_nb_empty);free(saved_unitclause_stack);
   free(saved_zeroLclause_stack);free(reason_stack);free(dirtyLiteral);//about var  14
   free(clausesRegion); free(conSet_of_learnc);
   for(i=0;i<NB_VAR+NB_VAR;i++){
     free(watcherlist[i].watchlit);
     free(literal_in[i].varindex);
   }
   free(watcherlist);
   free(literal_in);
   for(i=0;i<NB_CLAUSE;i++){
     if(Iclause_index_Lclause[i].vcap!=0)
	free(Iclause_index_Lclause[i].varindex);
   }
}

int  setOptions(){
 int i;
 HARD_WEIGHT=NB_CLAUSE;
 originalClauseN=NB_CLAUSE;
 maxLearntClause=originalClauseN/3;
 if(clauses_number_cap<originalClauseN+4*maxLearntClause)
    {printf("reset store space \n"); return FALSE;}
  for(i=0;i<NB_VAR;i++){
     var_reduce_state[i].level=NONE;
     var_reduce_state[i].reason=NO_REASON;
     var_reduce_state[i].Vstate=ACTIVE;
   }
  for(i=0;i<NB_VAR;i++){
     seen[i]=FALSE;
     varAssigns[i].current =l_Undef;
     varIndices[i]=NONE;
  }
  for(i=0;i<2*NB_VAR;i++)
    dirtyLiteral[i]=FALSE;
  for(i=0;i<NB_CLAUSE;i++){  //here, is better than in storeclause  
     clause_reduce_state[i].Cstate=ACTIVE;
     clause_reduce_state[i].involved=FALSE;
  }
  for(i=0;i<NB_CLAUSE;i++){
     Iclause_index_Lclause[i].vsize=0;
     Iclause_index_Lclause[i].vcap=0;
   }
  for(i=0;i<NB_VAR;i++)
     insertVar(i);
  return TRUE;
}


char * skipWhitespace(char* sin) {
  while ((*sin >= 9 && *sin <= 13) || *sin == 32)
     sin++; 
  return sin;
}

char * parseInt(char* in, int * literal) {
  int  val = 0,  _neg = 0;
  in=skipWhitespace(in);
  if (*in == '-'){ 
    _neg = 1; in++;}
  else if (*in == '+')  in++;
  if (*in < '0' || *in > '9'){ 
  	printf("PARSE ERROR! Unexpected char: %d\n", *in);}
  while (*in >= '0' && *in <= '9'){
    val = val*10 + (*in - '0');
    in++;
  }
  *literal= _neg ? -val : val; 
  return in;
}

int storeClauses(int * lits, int Csize){
  int cr,i;
  if(clausesRegion_size+Csize+1>=clausesRegion_cap){
     clausesRegion=(int *)realloc(clausesRegion,sizeof(int)*( clausesRegion_cap<<1));
	 if(clausesRegion==NULL) return FALSE;
     clausesRegion_cap= clausesRegion_cap<<1;
  }
  //store clause according the format: size state, literal1, literal2 and so on.
  cr=clausesRegion_size;
  clausesRegion[cr++]=Csize; 
  for(i=0;i<Csize;i++){
    clausesRegion[cr++]=lits[i];
  }
  attachClause(clauses_index_fill_pointer,clausesRegion_size,Csize); // add two literal watches by clause number and size
  if(attachLiteral(clauses_index_fill_pointer,lits,Csize)==FALSE) 
     return FALSE;
  push(clauses_index,clausesRegion_size); //store address of clause
  clausesRegion_size+=(Csize+1);
  return TRUE;
}

char * readClause(char *cin){
 int parsed_lit, var,lit1,lit2,lits_stack[1024],lits_stack_fill_pointer=0;
 int i,j,tautologie=FALSE;
   for (;;){
     cin = parseInt(cin, &parsed_lit);
  //   printf("%d \n",parsed_lit);
     if (parsed_lit == 0)  break;  //the clause end by 0, get one clause
     var = abs(parsed_lit)-1;  
     lit1=parsed_lit > 0 ? (var+var) :((var+var)^1);
     push(lits_stack,lit1);
   }
   //preprocess the clause, such as sorting 
  for(i=0;i<lits_stack_fill_pointer-1;i++){
     lit1=lits_stack[i];
     for(j=i+1;j<lits_stack_fill_pointer;j++){
       if(lit1>lits_stack[j]){
	  lit2=lit1;lit1=lits_stack[j];lits_stack[j]=lit2;}
	else if (lit1==lits_stack[j]){
         lits_stack[j]=lits_stack[lits_stack_fill_pointer-1];
         j--;lits_stack_fill_pointer--;lits_stack[lits_stack_fill_pointer]=NONE;
	}
       else if(lit1==(lits_stack[j]^1)){
	   tautologie=TRUE;  break;  // clause is satisfied
	}
    } 
    if (tautologie == TRUE) 
	 {NB_CLAUSE--; break;}
    else lits_stack[i] = lit1;
 }
 //store clause to clauseRegion
   if(tautologie==FALSE){
     if(lits_stack_fill_pointer==2){  //binary clause weight
       varActivity[lits_stack[0]>>1]++;
	varActivity[lits_stack[1]>>1]++;
     }
     storeClauses(lits_stack,lits_stack_fill_pointer);}
   return cin;
}

int buildInstance(char *input_file) {
  FILE* fp_in;
  char ch, word2[WORD_LENGTH],pLine[WORD_LENGTH];
  int i=0,k=0;uint32_t lsize;
  char * streambuffer;char * in;
  fp_in=fopen(input_file, "rb");
  if (fp_in == NULL) {
    return FALSE;
  }
  fseek(fp_in,0,SEEK_END);  //read file in buffer
  lsize=ftell(fp_in);
  rewind(fp_in);
  streambuffer=(char *)malloc(sizeof(char)*(lsize+1));
  if(streambuffer==NULL) 
     {printf("buffer store error \n"); return FALSE;}
  if(fread(streambuffer,1,lsize,fp_in)!=lsize)
     {printf("reading file to buffer error \n"); return FALSE;}
   streambuffer[lsize]=EOF;
   ch=streambuffer[k];   //remove useless information
   while (ch!='p') {
    while (ch!='\n') ch=streambuffer[++k];  
    ch=streambuffer[++k];
  } 
   i = 0; //get useful information such as var number
  while (ch!= '\n') {
    pLine[i++] = ch;
    ch=streambuffer[++k];
  }
  sscanf(pLine, "p %s %d %d %uint32_t", 
	 word2, &NB_VAR, &NB_CLAUSE, &HARD_WEIGHT);
  if (strcmp(word2, "cnf") == 0)
    instanceType = 0; // cnf
  else 
    instanceType = 1; // wcnf
  if (HARD_WEIGHT > 0) // For partial
    partial = 1;
  
  if(initStoreSpace(NB_VAR,NB_CLAUSE)==FALSE){ 
    printf("inite space malloc error \n");
    return FALSE;
  }
  //store each clause;
   in=&streambuffer[++k];
   for (;;){
     in=skipWhitespace(in);
     if (*in==EOF)
       break;
     else{
       in=readClause(in);}
   } 
  fclose(fp_in);
  free(streambuffer);
  if(partial==0)
    HARD_WEIGHT=NB_CLAUSE;
 #if 0
  k=0;
  for(i=0;i<clausesRegion_size;i++){
    k++;
    printf("%d  ",clausesRegion[i]);
    if(k==12) {k=0;printf("\n");}
  }
  for(k=0;k<2*NB_VAR;k++){
     for(i=0;i<watcherlist[k].wsize;i++)
       printf("%d,%d   ",watcherlist[k].watchlit[i].cn, watcherlist[k].watchlit[i].blocker);
     printf("\n");
 
  }
  for(k=0;k<2*NB_VAR;k++){
     printf("litreal_in %d \n",k);
     for(i=0;i<literal_in[k].vsize;i++)
	 printf("%d,  ",literal_in[k].varindex[i]);
      printf("\n");
  }
#endif
  return TRUE;
}

uint32_t verifySolution( ) {
  int i,j, cr,var,clause_truth;
  int* c;  uint32_t nb = 0;
  
  for (i = 0; i<originalClauseN; i++) {
    clause_truth = FALSE;
    cr=clauses_index[i];
    c=&clausesRegion[cr+1];
    for(j=0;j<clausesRegion[cr];j++)
      if (isTrue(c[j])==l_True) {
	  clause_truth = TRUE;
	break;
      }
    if (clause_truth == FALSE) {
      nb ++;
    }
  }
  return nb;
}

void remove_satisfied_clauses(int lit) {
  int i;int * clausesID;uint32_t size;
  size=literal_in[lit].vsize;
  clausesID=literal_in[lit].varindex;
  for(i=0;i<size;i++) {
     if(clause_stack_fill_pointer>clauses_number_cap)
	 printf("clause stack overflow\n");
     if (clause_reduce_state[clausesID[i]].Cstate== ACTIVE) {
      clause_reduce_state[clausesID[i]].Cstate= PASSIVE;
      push(clause_stack,clausesID[i]);
    }
  }
}

int backtracking(  ) {
  int literal,var,index;
  int *clause,addr;int i;
  NB_BACK++;
  while (trail_fill_pointer> 0) {
    literal=pop(trail);  var=literal>>1;
    var_reduce_state[var].Vstate=ACTIVE;
    NB_BRANCHE--;
    varAssigns[var].current=l_Undef;
    if (varAssigns[var].rest!= NONE){    
      for (index = saved_clause_stack[var];index < clause_stack_fill_pointer; index++){
	   addr=clauses_index[clause_stack[index]];
	   clause=&clausesRegion[addr+1];
	   if(var_reduce_state[clause[0]>>1].Vstate==ACTIVE||var_reduce_state[clause[1]>>1].Vstate==ACTIVE)
	       clause_reduce_state[clause_stack[index]].Cstate= ACTIVE;
	   else{
	   	clause_reduce_state[clause_stack[index]].Cstate=ZEROLEN;
              if(clause_stack[index]<originalClauseN) printf("zero back erro\n");  
	   }
	}
      clause_stack_fill_pointer = saved_clause_stack[var];
      unitclause_stack_fill_pointer=saved_unitclause_stack[var];
      NB_EMPTY=saved_nb_empty[var];
      for(index=saved_zeroLclause_stack[var];index<zero_learnt_clause_fill_pointer;index++){
	 clause_reduce_state[zero_learnt_clause[index]].Cstate=ACTIVE;
      }	
      zero_learnt_clause_fill_pointer=saved_zeroLclause_stack[var];
     #if 0
      printf("backtracking %d \n",literal); printf("backtracking empty %d \n",NB_EMPTY);
      printf("backtraking learnt clause state\n");
      for(i=originalClauseN;i<NB_CLAUSE;i++){
        printf(" %d ,",clause_reduce_state[i].Cstate);
      }
      #endif
      if (NB_EMPTY<UB) {
	varAssigns[var].current=varAssigns[var].rest;
	varAssigns[var].rest=NONE;
	var_reduce_state[var].level=++NB_BRANCHE;
	var_reduce_state[var].Vstate= PASSIVE;
	literal=var+var+varAssigns[var].current;
	push(trail,literal);
	if (reduce_clauses(literal)==NONE)
	  return NONE;
	remove_satisfied_clauses(literal);
	return TRUE;
//#if 0
	for(i=0;i<clause_stack_fill_pointer;i++){
         printf("%d ,", clause_stack[i]);
	}printf("\n");
//#endif
      } 
   } 
   insertVar(var);
  }
  return FALSE;
}

int remove_Leantc_of_Iclause(int Iclause){  //original clause is empty for patail assignments, remove it and learnt clauses containing it
 int * listclause,i,position,clause,start;
 start=clause_stack_fill_pointer;
 push(clause_stack,Iclause);
 clause_reduce_state[Iclause].Cstate=PASSIVE;
 i=start;
 while(i<clause_stack_fill_pointer){
   Iclause=clause_stack[i++];
   if(Iclause_index_Lclause[Iclause].vsize!=0){
     listclause=Iclause_index_Lclause[Iclause].varindex;
     for(position=0;position<Iclause_index_Lclause[Iclause].vsize;position++){
	 clause=listclause[position];
        if(clause_reduce_state[clause].Cstate!=PASSIVE){
           push(clause_stack,clause);
	    clause_reduce_state[clause].Cstate=PASSIVE;
        }
     }
   } 
 }
  return TRUE;
}

int reduce_clauses(int literal){
  struct VECW ws; struct Watcher w; struct Watcher * i,* j,* end; 
  int blocker,false_lit,first, k,cn,Addr,changeflag=FALSE; //cn means clause number
  int* clause; int a,b,Addr1,* clause1; int cn_stack[1000];int cn_stack_fill_pointer=0;
  i=watcherlist[literal].watchlit;
  j=watcherlist[literal].watchlit;
  end=i+watcherlist[literal].wsize;
  for(;i!=end;){
    changeflag=FALSE;
    blocker=i->blocker;
    cn=i->cn; 
#if 0
     push(cn_stack,cn);
    printf("cn is %d, blocker is %d    \n",cn,blocker);
    Addr1=clauses_index[cn];
    clause1=&clausesRegion[Addr1+1];
      for(b=0;b<clausesRegion[Addr1];b++)
	  printf("before rudecue %d ",clause1[b]);
      printf("\n");    
#endif   

    if(clause_reduce_state[cn].Cstate==ACTIVE){
      if(blocker==NONE){ //unit clause becomes empty clause
         if(cn<originalClauseN){
	     NB_EMPTY++;
	     if(NB_EMPTY>=UB){ while(i<end) *j++=*i++;watcherlist[literal].wsize-=(i-j);
	         return NONE;}
	     remove_Leantc_of_Iclause(cn);} 
	  else{
	     clause_reduce_state[cn].Cstate=ZEROLEN;
	     push(zero_learnt_clause,cn);  //learn clause is FALSE
          }
         *j++=*i++;continue;
       }
       false_lit=literal^1; 
       Addr=clauses_index[cn]; //inspect the clause in clauseRegion
       clause=&clausesRegion[Addr+1];
       if(clause[0]==false_lit){
          clause[0]=clause[1];
          clause[1]=false_lit;}
       i++;  //control the  for cycle
       w.blocker=clause[0];
       w.cn=cn;
       for(k=2;k<clausesRegion[Addr];k++){
          if(isTrue(clause[k])!=l_False){
            clause[1]=clause[k];
	     clause[k]=false_lit;
	     pushVetw(&watcherlist[clause[1]^1], cn, clause[0]);
	     changeflag=TRUE;  //new literal come into watching region
          }
       }
       if(changeflag==FALSE){
          *j++=w; //reserve the current clause in this watch,update the blocker 
          if(isTrue(clause[0])==l_False){
             if(cn<originalClauseN){
	         NB_EMPTY++;//printf("reduce empty clause %d \n",cn);
	         if(NB_EMPTY>=UB) { while(i<end) *j++=*i++;watcherlist[literal].wsize-=(i-j);
		   #if 0
		     for(a=0;a<watcherlist[literal].wsize;a++)
                    printf("%d,%d   ",watcherlist[literal].watchlit[a].cn, watcherlist[literal].watchlit[a].blocker);
                    printf("\n");
		   #endif
	            return NONE;}
	         remove_Leantc_of_Iclause(cn);
	      } 
	      else{
	         clause_reduce_state[cn].Cstate=ZEROLEN;
	          push(zero_learnt_clause,cn);
	      }
           }
         else
	     push(unitclause_stack,cn);
      }  
    continue;  //next clause,not reserve False clauses
    }
    *j++=*i++; //reserve satisfied clauses
  }
  watcherlist[literal].wsize=watcherlist[literal].wsize-(i-j);
#if 0
   printf("current watcher wsize %d \n",watcherlist[literal].wsize);
  for(a=0;a<watcherlist[literal].wsize;a++){
     printf("%d, %d   ",watcherlist[literal].watchlit[a].cn,watcherlist[literal].watchlit[a].blocker);
  }
  printf("\n");
#endif
//#if 0
   printf("reduce clause part\n");
   printf("involved watcher clause change \n");
   for(a=0;a<cn_stack_fill_pointer;a++){
     Addr=clauses_index[cn_stack[a]];
      clause=&clausesRegion[Addr+1];
      for(b=0;b<clausesRegion[Addr];b++)
	  printf("%d ",clause[b]);
      printf("\n");
   }
  printf("unit clause now \n");
  for(a=0;a<unitclause_stack_fill_pointer;a++){
    printf("%d ,",unitclause_stack[a]);
  }
  printf("zero clause stack now \n");
  for(a=0;a<zero_learnt_clause_fill_pointer;a++){
    printf("%d ,%d ,",zero_learnt_clause[a],clause_reduce_state[zero_learnt_clause[a]].Cstate);
  }
  printf("\n");
//#endif
  return TRUE;
}

int setpassive_Leantc_of_Iclause(int startpointer){
  int * listclause,i=0,position,clause,lclause;
  position=startpointer;
  while(position<clause_stack_fill_pointer){
    clause=clause_stack[position++];
    clause_reduce_state[clause].Cstate=PASSIVE;
    if(Iclause_index_Lclause[clause].vsize!=0){
       listclause=Iclause_index_Lclause[clause].varindex;
	for(i=0;i<Iclause_index_Lclause[clause].vsize;i++){
         lclause=listclause[i];
	  if(clause_reduce_state[lclause].Cstate!=PASSIVE&&clause_reduce_state[lclause].Cstate!=NEW_LCLAUSE//eliminate  NEW_LCLAUSE AND PASSIVE
	  	&&clause_reduce_state[lclause].involved==FALSE){//clause may be removed before
            push(clause_stack,lclause);
	     clause_reduce_state[lclause].involved=TRUE;
	  } 	
	}
    }
  } 
  for(i=startpointer;i<clause_stack_fill_pointer;i++)
    clause_reduce_state[clause_stack[i]].involved=FALSE;
  return TRUE;
}

//repalce learnt clause with conflict set when removing happens
int  remove_clauses_csets(  ){
int Rclause,position,i,clause,ii;
int start=clause_stack_fill_pointer;
 for(position=0;position<reason_stack_fill_pointer;position++){
    Rclause=reason_stack[position];
    if(clause_reduce_state[Rclause].Cstate!=PASSIVE&&clause_reduce_state[Rclause].involved==FALSE){//clause is satisfied
	 clause_reduce_state[Rclause].involved=TRUE;
	 push(clause_stack,Rclause);
        if(Rclause>=originalClauseN){
	    i=addr_of_learncSet[Rclause-originalClauseN];
	    clause=conSet_of_learnc[i];
	    while(clause!=NONE){
	       if(clause_reduce_state[clause].Cstate!=PASSIVE
		     &&clause_reduce_state[clause].involved==FALSE){//some clause maybe PASSIVE because they are satisfied.
                if(clause>=originalClauseN)
		    push(reason_stack,clause);
		  else{
                  push(clause_stack,clause);
//		    printf("%d, ",clause);
		    clause_reduce_state[clause].involved=TRUE;
		  }
	       }
	     clause=conSet_of_learnc[++i];
	    }
       }
    }	
 }
 //    printf("\n");
    setpassive_Leantc_of_Iclause(start);
 return TRUE;
}//not 


int my_reduce_clauses(int p ) {
  struct Watcher w;struct Watcher * i,* j,* end;
  int blocker,false_lit,first,cn,Addr,k,changeflag=FALSE;
  int* clause; int a;
  end=watcherlist[p].watchlit+watcherlist[p].wsize;
  for(i=j=watcherlist[p].watchlit;i!=end;){
    changeflag=FALSE;
    blocker=i->blocker;
    cn=i->cn; 
    if(clause_reduce_state[cn].Cstate==ACTIVE){
      if(blocker==NONE){ //unit clause becomes empty clause
         while(i<end)   
	     *j++=*i++;
	  watcherlist[p].wsize-=(i-j);
	  return cn;
       }       
	if(isTrue(blocker)==l_True){
          *j++=*i++;continue;
	}
       false_lit=p^1;
       Addr=clauses_index[cn];
       clause=&clausesRegion[Addr+1];
       if(clause[0]==false_lit){
          clause[0]=clause[1];
          clause[1]=false_lit;}
       i++;
	first=clause[0];
       w.blocker=clause[0];
       w.cn=cn;
	if(first!=blocker&&isTrue(first)==l_True){
          *j++=w;continue;
	}
       for(k=2;k<clausesRegion[Addr];k++){
          if(isTrue(clause[k])!=l_False){
            clause[1]=clause[k];
	     clause[k]=false_lit;
	     pushVetw(&watcherlist[clause[1]^1], cn, clause[0]);
	     changeflag=TRUE;
          }
       }
       if(changeflag==FALSE){
          *j++=w;
          if(isTrue(clause[0])==l_False){
	     while(i<end)   
	       *j++=*i++;
	     watcherlist[p].wsize-=(i-j);
            return cn;
           }
         else
	     push(my_unit_clause_stack,cn);
      }  
      continue;
    }
    *j++=*i++;   //reserve the satisfied clauses in watcherlist
  }
  watcherlist[p].wsize-=(i-j);
 #if 0
  printf("my_unit clause \n");
    for(a=0;a<my_unit_clause_stack_fill_pointer;a++)
	 printf("%d ", my_unit_clause_stack[a]);
    printf("\n");
  printf("trai  \n");
    for(a=0;a<trail_fill_pointer;a++)
	 printf("%d %d  %d,",trail[a],var_reduce_state[trail[a]>>1].Vstate,var_reduce_state[trail[a]>>1].reason);
    printf("\n");
#endif
  return NO_CONFLICT;
}

int satisfy_unitclause(int unitclause) {
  int literal, cr,clause, temp;	
  cr =clauses_index[unitclause];
  literal=clausesRegion[cr+1];
  if(var_reduce_state[literal>>1].Vstate==PASSIVE){
    if(var_reduce_state[clausesRegion[cr+2]>>1].Vstate==PASSIVE)
       return NO_CONFLICT;
    else{
       temp=clausesRegion[cr+1]; clausesRegion[cr+1]=clausesRegion[cr+2];clausesRegion[cr+2]=temp;
	literal=clausesRegion[cr+1];
    }
  }
  push(trail,literal);
  var_reduce_state[literal>>1].reason=unitclause;
  var_reduce_state[literal>>1].Vstate=PASSIVE;
  var_reduce_state[literal>>1].level=current_learnt_level;
  varAssigns[literal>>1].current=literal&1;
  if ((clause=my_reduce_clauses(literal))==NO_CONFLICT) 
     return NO_CONFLICT;
  else
     return clause;
}

int my_unitclause_process(int starting) {
  int unitclause, unitclause_position,clause, my_unitclause_position, my_unitclause;

  BCP_variable_index=trail_fill_pointer;
  for (unitclause_position = starting;unitclause_position < unitclause_stack_fill_pointer;unitclause_position++) {
    unitclause =unitclause_stack[unitclause_position];
    if (clause_reduce_state[unitclause].Cstate== ACTIVE) {
      my_unit_clause_stack_fill_pointer= 0;
      if ((clause=satisfy_unitclause(unitclause)) != NO_CONFLICT) 
	  return clause;
      else {
	  for (my_unitclause_position = 0;my_unitclause_position <my_unit_clause_stack_fill_pointer;my_unitclause_position++) {
	     my_unitclause = my_unit_clause_stack[my_unitclause_position];
	     if (clause_reduce_state[my_unitclause].Cstate== ACTIVE) {
	       if ((clause=satisfy_unitclause(my_unitclause)) != NO_CONFLICT) 
	         return clause;	       
	     }
	  }//end for
       }
     }
  }
  return NO_CONFLICT;
}

#define CLAUSE_INDEX_ISIZE  524288

int  add_learntC_clause_index(  ){
   int i, * position,iclause;
   for(i=prior_confsets;i<conSet_of_learnc_fill_pointer-1;i++){
     iclause=conSet_of_learnc[i];
     if(Iclause_index_Lclause[iclause].vcap==0){
	 Iclause_index_Lclause[iclause].varindex=(int *)malloc((CLAUSE_INDEX_ISIZE) * sizeof(int));
        if(Iclause_index_Lclause[iclause].varindex==NULL) return FALSE;
	 Iclause_index_Lclause[iclause].vcap=CLAUSE_INDEX_ISIZE;
     }
     if(Iclause_index_Lclause[iclause].vsize>=Iclause_index_Lclause[iclause].vcap){
        Iclause_index_Lclause[iclause].varindex=(int *)realloc(Iclause_index_Lclause[iclause].varindex,sizeof(int)*2*Iclause_index_Lclause[iclause].vcap);
        if(Iclause_index_Lclause[iclause].varindex==NULL) return FALSE;
	 Iclause_index_Lclause[iclause].vcap*=2;
     }
     position=Iclause_index_Lclause[iclause].varindex;     
     position[Iclause_index_Lclause[iclause].vsize++]=NB_CLAUSE;//add lerant clause as first node
  }
    return TRUE;
}


int analyze_conflict(int cfclause){
   int PathC=0,i=0,UIP_index,lclause,addr,conflict_clause,literal,var,j;
   int flaglit=NONE,*clause; 
   int seen_variables_revert[1024];
   int seen_variables_revert_fill_pointer=0;  
      conflict_clause=cfclause;
      conflict_number++; //computer the valid analyze number 
      UIP_index=trail_fill_pointer-1;
      prior_confsets=conSet_of_learnc_fill_pointer;
      temp_learnt_clause_fill_pointer=1;

   do{
      addr=clauses_index[conflict_clause];
      clause=&clausesRegion[addr+1];
     for(j=(flaglit==NONE)?0:1;j<clausesRegion[addr];j++){
	literal=clause[j];  var=literal>>1; 
       if(seen[var]!=TRUE&&var_reduce_state[var].level>=0) {
            updateVar(var);
	     seen[var]=TRUE;
	     if(var_reduce_state[var].level>=current_learnt_level){
		  PathC++;
              }
	     else{
		  push(temp_learnt_clause,literal);
		  push(seen_variables_revert,var);
	     }    
        }
      }
    // if(clause_weight[conflict_clause]<HARD_WEIGHT)
    if(conSet_of_learnc_fill_pointer<conSet_of_learnc_cap-2)
       push(conSet_of_learnc,conflict_clause);//record the FUIP conflictset
    else{
       conSet_of_learnc=(int *)realloc(conSet_of_learnc,conSet_of_learnc_cap*2*sizeof(int));
	if(conSet_of_learnc==NULL) {printf("conset room is not enough\n"); return FALSE;}
	conSet_of_learnc_cap*=2;
	push(conSet_of_learnc,conflict_clause);
    }
	
    while(!seen[trail[UIP_index--]>>1]&&UIP_index>BCP_variable_index-2&&(UIP_index>=0));//next conflict clause
    if(UIP_index<BCP_variable_index-2)
	 break;
    flaglit=trail[UIP_index+1]; //get the next conflict variable
    if(var_reduce_state[flaglit>>1].reason!=NO_REASON){
      conflict_clause=var_reduce_state[flaglit>>1].reason;//conflict structure is chain,value maybe NONE
    }
    seen[flaglit>>1]=FALSE;
    PathC--;
   }while(PathC>0);
  temp_learnt_clause[0]=flaglit^1; // FUIP must be 0 unit 
  push(conSet_of_learnc,NONE);
   for(i=0;i<seen_variables_revert_fill_pointer;i++)
     seen[seen_variables_revert[i]]=FALSE;
 //special case:R3,R4
  if(conSet_of_learnc_fill_pointer-prior_confsets==2){  
     conSet_of_learnc_fill_pointer=prior_confsets;
     clause=&clausesRegion[clauses_index[cfclause]];;
     for(i=0;i<clause[0];i++){
	 literal=clause[i+1];
        seen[literal>>1]=FALSE;
     }
     return FALSE;
  }
  return TRUE;
}

void confirmDeleteC( ){
   int i,j,cn,cr,count=0;int * clause;int saved;
   saved=learntclause_fill_pointer;
   clauseDelete_fill_pointer=0;
   for(i=0;i<learntclause_fill_pointer;i++){
     cn=learntclause[i];
     if(count>=(saved/2))
	 break;
     if(clause_reduce_state[cn].Cstate==ACTIVE){
        push(clauseDelete,cn);
	 if(Iclause_index_Lclause[cn].vcap!=0){
	   free(Iclause_index_Lclause[cn].varindex);
	   Iclause_index_Lclause[cn].vcap=0;}
	 clauseDelMark[cn-originalClauseN]=TRUE;
	 learntclause[i]=learntclause[learntclause_fill_pointer-1];
	 learntclause_fill_pointer--;
	 i--;
	 count++;
     }
   }
}

int  create_learnt_clause( ){
  int i,literal,cr;int * clause; int k;
 
  if(clausesRegion_size+temp_learnt_clause_fill_pointer+1>=clausesRegion_cap){
     clausesRegion=(int *)realloc(clausesRegion,sizeof(int)*(clausesRegion_cap<<1));
	 if(clausesRegion==NULL) return FALSE;
     clausesRegion_cap=clausesRegion_cap<<1;
  }
  cr=clausesRegion_size;
  clausesRegion[cr++]=temp_learnt_clause_fill_pointer; 
  for(i=0;i<temp_learnt_clause_fill_pointer;i++){
     literal=temp_learnt_clause[i];
    clausesRegion[cr++]=literal;
    //updateVar(literal>>1);
  }
  attachClause(NB_CLAUSE,clausesRegion_size,temp_learnt_clause_fill_pointer);
  attachLiteral(NB_CLAUSE, temp_learnt_clause, temp_learnt_clause_fill_pointer);
  clause_reduce_state[NB_CLAUSE].Cstate=NEW_LCLAUSE;
  clause_reduce_state[NB_CLAUSE].involved=FALSE; 
  push(clauses_index,clausesRegion_size);
  push(clause_stack,NB_CLAUSE);
  push(learntclause,NB_CLAUSE);
  clauseDelMark[NB_CLAUSE-originalClauseN]=FALSE;
  clausesRegion_size+=temp_learnt_clause_fill_pointer+1;
  addr_of_learncSet[NB_CLAUSE-originalClauseN]= prior_confsets;//buliding  mapping   
  Iclause_index_Lclause[NB_CLAUSE].vcap=0;
  Iclause_index_Lclause[NB_CLAUSE].vsize=0;
  NB_CLAUSE++;
  return TRUE;
}

int store_csets_of_learntc(int cfclause){
  int var_index,bvar=-1, i,var,csize,literal;
  int * clause;
  var_index=trail_fill_pointer-1;
  while(var_index>=BCP_variable_index-1){
     clause=&clausesRegion[clauses_index[cfclause]+1];
     csize=clausesRegion[clauses_index[cfclause]];
     for(i=0;i<csize;i++){
	 literal=clause[i];
	 var=literal>>1;
        if(seen[var]!=TRUE&&var_reduce_state[var].level==current_learnt_level&&var!=bvar) 
          seen[var]=TRUE;      
     }
     push(reason_stack,cfclause);
     while((!seen[trail[var_index--]>>1])&&(var_index>=BCP_variable_index-2)&&(var_index>=0));
     if(var_index<BCP_variable_index-2)
	 break;
     bvar=trail[var_index+1]>>1; 
     seen[bvar]=FALSE;
     if(var_reduce_state[bvar].reason!=NO_REASON){
	 cfclause=var_reduce_state[bvar].reason;
     }
  }
  return TRUE;
}

void reset_context(int saved_clause_stack_fill_pointer, 
		   int saved_unitclause_stack_fill_pointer, 
		   int saved_variable_stack_fill_pointer) {
  int index, var;
    
  for(index=saved_variable_stack_fill_pointer; index<trail_fill_pointer; index++) {
    var=trail[index]>>1;
    var_reduce_state[var].Vstate=ACTIVE;
    var_reduce_state[var].reason=NO_REASON;
    varAssigns[var].current=l_Undef;
  }
  trail_fill_pointer=saved_variable_stack_fill_pointer;
  unitclause_stack_fill_pointer=saved_unitclause_stack_fill_pointer;
}

void reset_clause_context(int start){
  int clause,length,position,addr;
  int var, k;int * c;int i;
  position=start;
  while(position<clause_stack_fill_pointer){
     clause=clause_stack[position++];
     if(clause<originalClauseN)
	  clause_reduce_state[clause].Cstate=ACTIVE;
     else{
	addr=clauses_index[clause];
	c=&clausesRegion[addr+1];
       if(clause_reduce_state[clause].Cstate==NEW_LCLAUSE){
         if(clause<originalClauseN)
	     printf("new clause error\n");
         if(var_reduce_state[c[0]>>1].Vstate==ACTIVE){
	    push(unitclause_stack,clause);
	    clause_reduce_state[clause].Cstate=ACTIVE;
	  }
	  else {
	    push(zero_learnt_clause,clause);
           clause_reduce_state[clause].Cstate=ZEROLEN;
	  }	    
       }
      else if(clause_reduce_state[clause].Cstate==PASSIVE){
	  if(var_reduce_state[c[0]>>1].Vstate==ACTIVE||var_reduce_state[c[1]>>1].Vstate==ACTIVE)
	    clause_reduce_state[clause].Cstate=ACTIVE;
	  else 	    
           clause_reduce_state[clause].Cstate=ZEROLEN;	  	
      }
    }
 }
//#if 0
  printf("reset clause state part\n");
     for(i=0;i<clause_stack_fill_pointer;i++)
       printf("%d ,",clause_reduce_state[clause_stack[i]].Cstate);
     printf("\n");
//#endif
 clause_stack_fill_pointer=start;
}

int lookahead_by_up(uint32_t nb_conflicts) {
  int saved_unitclause_stack_fill_pointer, 
       saved_variable_stack_fill_pointer, my_saved_clause_stack_fill_pointer;
  int  clause,i;

  saved_unitclause_stack_fill_pointer = unitclause_stack_fill_pointer;
  saved_variable_stack_fill_pointer=trail_fill_pointer;
  my_saved_clause_stack_fill_pointer= clause_stack_fill_pointer;
  current_learnt_level=NB_BRANCHE;
 //if find conflict, conflict clasuses are stored in clause_stack, clause_state is P.
 //learnt clause is in clause_stack, clause_state is P and length is 1.
 //those clause whose conflict clause set includes conflicting clause, clause_state is P.
  while ((clause=my_unitclause_process(0))!=NO_CONFLICT) {
    reason_stack_fill_pointer=0;
    if(analyze_conflict(clause)!=FALSE){
	 add_learntC_clause_index( );   //add literal_in index for each conflict clause 
        create_learnt_clause( );}
    store_csets_of_learntc(clause);
//#if 0
    printf("up detection part\n");
    printf("learnt clause is \n");
    for(i=0;i<temp_learnt_clause_fill_pointer;i++)
	 printf("%d ", temp_learnt_clause[i]);
    printf("\n");
    printf("the learnt clause's conflict set \n");
      i=addr_of_learncSet[NB_CLAUSE-originalClauseN-1];
        while(conSet_of_learnc[i]!=NONE){
           printf("%d ,",conSet_of_learnc[i]);
           i++;
        }

    printf("variable stack \n");
    for(i=0;i<trail_fill_pointer;i++)
	 printf("%d ", trail[i]);
    printf("\n");

    printf("unit clause \n");
    for(i=0;i<unitclause_stack_fill_pointer;i++)
	 printf("%d ", unitclause_stack[i]);
    printf("\n");
 
//#endif
    my_saved_clause_stack_fill_pointer=clause_stack_fill_pointer; //reserve the new learnt clause.it's state is NEW_LCLAUSE
    reset_context(my_saved_clause_stack_fill_pointer, 
		saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer); 
    remove_clauses_csets( );
    my_saved_clause_stack_fill_pointer=clause_stack_fill_pointer;
//#if 0
printf("clause stack is \n");
for(i=0;i<clause_stack_fill_pointer;i++)
	 printf("%d ,",clause_stack[i]);
    printf("\n");
//#endif
    nb_conflicts++;
    if (nb_conflicts+NB_EMPTY>=UB) 
      break;
  }
  reset_context(my_saved_clause_stack_fill_pointer, 
		saved_unitclause_stack_fill_pointer,
		saved_variable_stack_fill_pointer); 
  return nb_conflicts;
}


int lookahead() {
  int saved_clause_stack_fill_pointer, saved_unitclause_stack_fill_pointer, saved_variable_stack_fill_pointer;
  int clause, i,position;
  uint32_t conflict=0;
  saved_clause_stack_fill_pointer= clause_stack_fill_pointer;
  saved_unitclause_stack_fill_pointer =unitclause_stack_fill_pointer;
  saved_variable_stack_fill_pointer=trail_fill_pointer;

  for(position=0;position<zero_learnt_clause_fill_pointer;position++){
     reason_stack_fill_pointer=0;
     clause=zero_learnt_clause[position];// printf("zero stack %d \n",clause_reduce_state[clause].Cstate);
     if(clause_reduce_state[clause].Cstate==ZEROLEN){//necessary limited, some learnt clauses maybe have been passive for remove_clauses_csets
	 conflict++;//  printf("NB_EMPTY %d \n",NB_EMPTY);
	 if(conflict+NB_EMPTY>=UB)
	    return NONE;
	 push(reason_stack,clause);
        remove_clauses_csets( );
     }
  }
//#if 0
  printf("move zero part\n");
  for(i=0;i<clause_stack_fill_pointer;i++)
    printf("%d ,",clause_stack[i]);
  printf("\n");
//#endif
  conflict=lookahead_by_up(conflict);
  if(conflict+NB_EMPTY>=UB)
     return NONE;
  else{
     reset_clause_context(saved_clause_stack_fill_pointer);
     return conflict;}
}

void  removeLiteralIndex(){
  int lit,cn,i,k,cr;int *clause,*delIndex;
  for(k=0;k<clauseDelete_fill_pointer;k++){
     cn=clauseDelete[k];
     cr=clauses_index[cn];
     clause=&clausesRegion[cr+1];
     for(i=0;i<clausesRegion[cr];i++)
	dirtyLiteral[clause[i]]=TRUE;
  }
  for(lit=0;lit<NB_VAR*2;lit++){
     if(dirtyLiteral[lit]==TRUE){
	delIndex=literal_in[lit].varindex;
       for(k=0;k<literal_in[lit].vsize;k++){
          if(delIndex[k]>=originalClauseN&& clauseDelMark[delIndex[k]-originalClauseN]==TRUE){
             delIndex[k]=delIndex[--literal_in[lit].vsize];
	      k--;
	  }
	}
      dirtyLiteral[lit]=FALSE;
     }
  }
}

void removeWatchIndex(  ){
  int lit,cn,k,cr;struct Watcher * i, *j,*end;int *clause;
  for(k=0;k<clauseDelete_fill_pointer;k++){
     cn=clauseDelete[k];
     cr=clauses_index[cn];    
     clause=&clausesRegion[cr+1];
     dirtyLiteral[clause[0]^1]=TRUE;
     dirtyLiteral[clause[1]^1]=TRUE;
  }
  for(lit=0;lit<NB_VAR*2;lit++){
     if(dirtyLiteral[lit]==TRUE){
	 i= watcherlist[lit].watchlit;
	 end=i+(watcherlist[lit].wsize-1);
	 while(i<=end){
           cn=i->cn;
	    if(cn>=originalClauseN&& clauseDelMark[cn-originalClauseN]==TRUE){
              *i--=*end--;
		watcherlist[lit].wsize--;
	    }
	   i++;
	 }
     dirtyLiteral[lit]=FALSE;
     }     
  }
}

int add_learntC_Index(int clause,int lclause){
int * position;
   if(Iclause_index_Lclause[clause].vsize>=Iclause_index_Lclause[clause].vcap){
        Iclause_index_Lclause[clause].varindex=(int *)realloc(Iclause_index_Lclause[clause].varindex,sizeof(int)*2*Iclause_index_Lclause[clause].vcap);
        if(Iclause_index_Lclause[clause].varindex==NULL) return FALSE;
	 Iclause_index_Lclause[clause].vcap*=2;
     }
     position=Iclause_index_Lclause[clause].varindex;     
     position[Iclause_index_Lclause[clause].vsize++]=lclause; 
  return TRUE;
}

int removeLearntSet(){
  int i,addr,j,saved,clause;int k;int *p;
  int *to;uint32_t to_size=0;
   to=(int *)malloc(sizeof(int)*conSet_of_learnc_cap);   
   if(!to) {printf("to error \n"); return FALSE;}
   for(i=originalClauseN;i<NB_CLAUSE;i++){
     if(clauseDelMark[i-originalClauseN]==FALSE){
	 saved=to_size; reason_stack_fill_pointer=0;
        addr=addr_of_learncSet[i-originalClauseN];
	 while((clause=conSet_of_learnc[addr])!=NONE){
	   if(clause_reduce_state[clause].involved!=TRUE){
	     if(clause>originalClauseN&&clauseDelMark[clause-originalClauseN]==TRUE){
              push(reason_stack,clause);
              clause_reduce_state[clause].involved=TRUE;
	     }  
	     else{
              to[to_size++]=conSet_of_learnc[addr];
              clause_reduce_state[clause].involved=TRUE;
	     }
	   }
	   addr++;
	 }//end while
	 for(j=0;j<reason_stack_fill_pointer;j++){
           addr=addr_of_learncSet[j-originalClauseN];
           while((clause=conSet_of_learnc[addr])!=NONE){
	     if(clause_reduce_state[clause].involved!=TRUE){
	      if(clause>originalClauseN&&clauseDelMark[clause-originalClauseN]==TRUE){
               push(reason_stack,clause);
               clause_reduce_state[clause].involved=TRUE;
	     }  
	     else{
              to[to_size++]=conSet_of_learnc[addr];
              clause_reduce_state[clause].involved=TRUE;
		add_learntC_Index(clause,i);
	     }
	   }
	   addr++;
	 }

	 }
	 to[to_size++]=NONE;
        addr_of_learncSet[i-originalClauseN]=saved;
	for(k=saved;k<to_size-1;k++){
         clause_reduce_state[k].involved=FALSE;
	}
	for(k=0;k<reason_stack_fill_pointer;k++){
         clause_reduce_state[k].involved=FALSE;
	}
     }
   }
   conSet_of_learnc_fill_pointer=to_size;
   free(conSet_of_learnc);
   conSet_of_learnc=to; 
   return TRUE;
}

int reduce_clausesDB(){
int i;int * to;int addr,k,saved,sz,j;int *p;
   to=(int *)malloc(sizeof(int)*clausesRegion_cap);   
   if(!to) {printf("to error \n"); return FALSE;}
   addr=clauses_index[originalClauseN];
   for(i=0;i<addr;i++){
      to[i]=clausesRegion[i];
   }
   for(k=originalClauseN;k<NB_CLAUSE;k++){
      if(clauseDelMark[k-originalClauseN]!=TRUE){
	 saved=addr;
        sz=clausesRegion[clauses_index[k]];
	 for(j=0;j<=sz;j++){
          to[addr++]=clausesRegion[clauses_index[k]+j];
	 }
       clauses_index[k]=saved;
	}
   }
   clausesRegion_size=addr;
   free(clausesRegion);
   clausesRegion=to;
   return TRUE;
}


int pickBranchLit( ){
  int literal,chosen_var=NONE;
  int i, k;
  BRANCH_NODE++;
  if (lookahead( )==NONE)
    return NONE;  //LB>=UB
  #if 0
  if(learntclause_fill_pointer>=maxLearntClause){
     confirmDeleteC(  );   
     removeLiteralIndex();
     removeWatchIndex();
     removeLearntSet();
     DelCount++;
  }
  if(DelCount==2)	{
     reduce_clausesDB();
     DelCount=0;
  }
 #endif
  if(varCandidate_STACK_fill_pointer!=0)
    chosen_var=removeMax_var(); 
#if 0
  printf("after UP \n");
  for(k=0;k<2*NB_VAR;k++){
     for(i=0;i<watcherlist[k].wsize;i++)
       printf("%d,%d   ",watcherlist[k].watchlit[i].cn, watcherlist[k].watchlit[i].blocker);
     printf("\n");
 
  }
  k=0;
  for(i=0;i<clausesRegion_size;i++){
    k++;
    printf("%d  ",clausesRegion[i]);
    if(k==12) {k=0;printf("\n");}
  }
 printf("new chosen var %d \n",chosen_var);
 for(i=0;i<varCandidate_STACK_fill_pointer;i++)
    printf(" %d, %d \n",varCandidate_STACK[i], varActivity[varCandidate_STACK[i]]);
 for(i=0;i<NB_VAR;i++)
    printf("%d ",varIndices[i]);
 printf("\n");
 
#endif
  if (chosen_var== NONE) return FALSE; //no variable is not assigned
  saved_clause_stack[chosen_var] = clause_stack_fill_pointer;
  saved_unitclause_stack[chosen_var] = unitclause_stack_fill_pointer;
  saved_nb_empty[chosen_var]=NB_EMPTY;
  saved_zeroLclause_stack[chosen_var]=zero_learnt_clause_fill_pointer;
  varAssigns[chosen_var].current =l_False;  // branch var choose -x first ,then x
  varAssigns[chosen_var].rest =l_True;
  literal=chosen_var+chosen_var+varAssigns[chosen_var].current;
  if (var_reduce_state[chosen_var].Vstate==PASSIVE)
    printf("ERROR: Assigning passive variable.\n");
  var_reduce_state[chosen_var].Vstate=PASSIVE;
  var_reduce_state[chosen_var].level=++NB_BRANCHE;
  push(trail,literal);
  if (reduce_clauses(literal)==NONE)
    return NONE;  //LB>=UB
  remove_satisfied_clauses(literal);
#if 0
  printf("satisfied clause stack now \n");
  for(k=0;k<clause_stack_fill_pointer;k++){
    printf("%d ,",clause_stack[k]);
  }
#endif
  return TRUE;  //LB<UB
} 

void dpl(){
  uint64_t nb;
  int i;
  do {
    if (trail_fill_pointer==NB_VAR) {
      UB = NB_EMPTY;   
    nb = verifySolution( );
    if (nb != NB_EMPTY)
      printf("ERROR: Solution verification fails, real_empty = %u, NB_EMPTY = %u.\n", 
	       nb, NB_EMPTY);
      printf("o %u\n", UB);
    for (i = 0; i < NB_VAR; i++)
	varBestValue[i] = varAssigns[i].current;
    while (backtracking()==NONE);
      if (trail_fill_pointer==0)  
	break;
    }

    if (pickBranchLit()==NONE)
     while (backtracking()==NONE);
  } while (trail_fill_pointer> 0);
}


int main(int argc,char *argv[])
{ int i; 
    char saved_input_file[WORD_LENGTH];
    FILE *fp_time;
    struct rusage starttime, endtime;
    if (argc <= 1) {
      printf("Using format: %s input_instance [-l]\n\t-l: without local search.", argv[0]);
      return FALSE;
    }
    for (i=0; i<WORD_LENGTH; i++)
       saved_input_file[i]=argv[1][i];
    getrusage(RUSAGE_SELF, &starttime );

    printf("c ---------------------------------\n");
    printf("c -------Partial maxsatzL------------\n");
    printf("c ---------------------------------\n");
    printf("c solving instance %s...\n", argv[1]);

    switch (buildInstance(argv[1])) {
    case FALSE:
       printf("ERROR: Input file error\n");
       return FALSE;
    case TRUE:
       UB=NB_CLAUSE;
       printf("o %u\n", UB);
       if (UB != 0) {
        if(setOptions()==FALSE){
	    freespace(); break;};
        dpl();
	 freespace();
       }
      break;
  case NONE:
     freespace( );
     printf("An empty resolvant is found!\n"); break;
  }

  getrusage( RUSAGE_SELF, &endtime );

 //output the instance status
   if (UB >= HARD_WEIGHT) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s OPTIMUM FOUND\n");
    printf("v");
    for (i = 0; i < NB_VAR; i++) {
      if (varBestValue[i] ==l_False)
	printf(" -%d", i + 1);
      else
	printf(" %d", i + 1);
    }
    printf(" 0\n");
  }
  printf("c Learned clauses = %u\n", NB_CLAUSE-originalClauseN);
  printf("c NB_NODE= %u, NB_BACK= %u, conflict_number= %u \n", 
	  BRANCH_NODE, NB_BACK,conflict_number);
  
  printf ("c Program terminated in %d seconds.\n",
	  ((int)(endtime.ru_utime.tv_sec - starttime.ru_utime.tv_sec)));
    return 0;
}
