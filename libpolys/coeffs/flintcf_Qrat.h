/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/

/*
* ABSTRACT: flint: rational functions over Q (using fmpq_mpoly)
*/

#ifndef FLINTCF_QRAT_H
#define FLINTCF_QRAT_H

#include "misc/auxiliary.h"
#ifdef HAVE_FLINT

typedef struct
{
   fmpq_mpoly_t num;
   fmpq_mpoly_t den;
} fmpq_rat_struct;

typedef struct /* this is a temporary hack until we define this structure properly */
{
   fmpq_mpoly_ctx_struct * ctx;
} fmpq_rat_data_struct;

BOOLEAN flintQrat_InitChar(coeffs cf, void * infoStruct);

coeffs flintQratInitCfByName(char *s, n_coeffType n);
#endif

#endif

