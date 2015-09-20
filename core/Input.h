
#include <stdio.h>
#include <zlib.h>
//#include "SolverTypes.h"
#include "Solver.h"

namespace zmaxsat {
//==============================================================================================================
//data structure for input function --parseutils.h
static const int buffer_size = 1048576;
class StreamBuffer {
    gzFile        in;
    unsigned char buf[buffer_size];
    int           pos;
    int           size;

    void assureLookahead() {
        if (pos >= size) {
            pos  = 0;
            size = gzread(in, buf, sizeof(buf)); } }
//circulate reading
public:
    explicit StreamBuffer(gzFile i) : in(i), pos(0), size(0) { assureLookahead(); }

    int  operator *  () const { return (pos >= size) ? EOF : buf[pos]; }
    void operator ++ ()       { pos++; assureLookahead(); }
    int  position    () const { return pos; }
};

//-------------------------------------------------------------------------------------------------
// End-of-file detection functions for StreamBuffer and char*:
static inline bool isEof(StreamBuffer& in) { return *in == EOF;  }
static inline bool isEof(const char*   in) { return *in == '\0'; }
//-------------------------------------------------------------------------------------------------
// Generic parse functions parametrized over the input-stream type.
template<class B>
static void skipWhitespace(B& in) {
    while ((*in >= 9 && *in <= 13) || *in == 32)
        ++in; }

template<class B>
static void skipLine(B& in) {
    for (;;){
        if (isEof(in)) return;
        if (*in == '\n') { ++in; return; }
        ++in; } }
 //函数功能是把字符串转换成数字
template<class B>
static int parseInt(B& in) {
    int     val = 0;
    bool    neg = false;
    skipWhitespace(in);
    if      (*in == '-') neg = true, ++in;
    else if (*in == '+') ++in;
    if (*in < '0' || *in > '9') fprintf(stderr, "PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    while (*in >= '0' && *in <= '9')
        val = val*10 + (*in - '0'),
        ++in;
    return neg ? -val : val; }
// String matching: in case of a match the input iterator will be advanced the corresponding
// number of characters.
template<class B>
static bool match(B& in, const char* str) {
    int i;
    for (i = 0; str[i] != '\0'; i++)
        if (in[i] != str[i])
            return false;
    in += i;
	return true;
}

// String matching: consumes characters eagerly, but does not require random access iterator.
template<class B>
static bool eagerMatch(B& in, const char* str) {
    for (; *str != '\0'; ++str, ++in)
        if (*str != *in)
            return false;
    return true; }

//=================================================================================================
// input fuctions for instance:

template<class B, class Solver>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit)-1;
        while (var>= S.nVars()) S.newVar();
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~ mkLit(var) );
    }
}

template<class B, class Solver>
static void parse_DIMACS_main(B& in, Solver& S) {
    vec<Lit> lits;
    int cnt= 0;
    for (;;){
        skipWhitespace(in); //略过空格
        if (*in == EOF) break; //读文件结束
        else if (*in == 'p'){
           if (eagerMatch(in, "p cnf")){
                S.setnVars(parseInt(in)); //获取变元个数
                S.setnClauses(parseInt(in)); //获取子句个数
                S.setisWeight(0);
           }
	       else if(eagerMatch(in, "p wcnf")){
                S.setnVars(parseInt(in)); //获取变元个数
                S.setnClauses(parseInt(in)); //获取子句个数
                S.setisWeight(1);
           	    if(*in!='\n'){
		          skipWhitespace(in);
		          int hardweight=0;
		          while (*in >= '0' && *in <= '9'){
                    hardweight= hardweight*10 + (*in - '0'),
                    ++in;
                  }
		         S.setHardWeight(hardweight);
           	    }
                if(S.getHardWeight()>0)
		          S.setPartial(1);
	       }
        }
        else if(*in == 'c' || *in!= 'p')
            skipLine(in);// 略去文件开始部分的说明性信息
        else{   //开始读入每个子句
            cnt++;
            readClause(in, S, lits);
	        S.addClause(lits);
        }
 }//end for
 if (cnt!=S.getnClauses())
        fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
}

// Inserts problem into solver.
//
template<class Solver>
static void buildInstance(gzFile input_stream, Solver& S) {
    StreamBuffer in(input_stream); //为文件分配一个读入的字符流缓存
    parse_DIMACS_main(in, S); }//读入算例的子句等信息

//=================================================================================================
}

