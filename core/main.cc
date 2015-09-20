#define INT32_MIN   (-0x7fffffff-1)
#define INT64_MIN   (-0x7fffffffffffffff-1)
#define INT32_MAX   0x7fffffff
#define INT64_MAX   0x7fffffffffffffff
#define UINT32_MAX  0xffffffff
#define UINT64_MAX  0xffffffffffffffff
#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "../utils/System.h"
#include "Input.h"
//#include "../utils/Options.h"
//#include "../core/Dimacs.h"
#include "../core/Solver.h"
using namespace zmaxsat;

int main(int argc,char *argv[])
{
    struct rusage starttime, endtime;
    if (argc <= 1) {
      printf("Using format: %s input_instance [-l]\n\t-l: without local search.", argv[0]);
      return FALSE;
    }
    Solver s;
    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if(in == NULL)
      printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
    getrusage(RUSAGE_SELF, &starttime );
    printf("--------------------------------------\n");
    printf("----------Partial zmaxsat------------\n");
    printf("--------------------------------------\n");
    printf("zmaxsat solving instance %s...\n", argv[1]);
   buildInstance(in,s);
    gzclose(in);
    s.dpl();
 //output the instance status
   if (s.getUB() >= s.getHardWeight()) {
    printf("s UNSATISFIABLE\n");
  } else {
    printf("s OPTIMUM FOUND\n");
    printf("v");
    for (int i = 0; i < s.getnVars(); i++) {
      if (s.value(i) ==l_False)
	printf(" -%d", i + 1);
      else
	printf(" %d", i + 1);
    }
    printf(" 0\n");
  }
  printf("Learned clauses = %u\n", s.getnClauses()-s.getoriginalClauseN());
  printf("NB_NODE= %u, NB_BACK= %u, conflict_number= %u \n",
	  s.getBranchNode(), s.getNbBack(),s.getconflictNumber());

  printf ("Program terminated in %d seconds.\n",
	  ((int)(endtime.ru_utime.tv_sec - starttime.ru_utime.tv_sec)));

    return 0;
}
