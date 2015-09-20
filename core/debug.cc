#include "../core/Solver.h"
#include "../mtl/Vec.h"
#include <stdarg.h>
namespace zmaxsat {

vec<Lit>& createVecLit(int num,...)
{
    va_list ArgList;
    vec<Lit> tmp;
    for(int i=1;i<=num;i++)
    {
        int arg=va_arg(ArgList,int);
        tmp.push(mkLit(arg>0?arg:-arg,arg>0?true:false));
    }
    va_end(ArgList);
    return tmp;
}

}
