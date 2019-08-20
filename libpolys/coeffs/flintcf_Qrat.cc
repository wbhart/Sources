/****************************************
*  Computer Algebra System SINGULAR     *
****************************************/
/*
* ABSTRACT: flint: rational functions over Q (using fmpq_mpoly)
*/
#include <ctype.h> /* isdigit*/

#include "misc/auxiliary.h"

#ifdef HAVE_FLINT

#include <flint/flint.h>
#include <flint/fmpq_mpoly.h>
#include "factory/factory.h"

#include "coeffs/coeffs.h"

#include "coeffs/numbers.h"
#include "coeffs/longrat.h"

typedef fmpq_rat_struct *fmpq_rat_ptr;
typedef fmpq_mpoly_struct *fmpq_mpoly_ptr;
typedef fmpq_ctx_struct *fmpq_ctx_ptr;
typedef fmpz *fmpz_ptr;

/******************************************************************************
* Helper functions
******************************************************************************/

/*2
* extracts a long integer from s, returns the rest
*/
static char * nlEatLong(char *s, mpz_ptr i)
{
  const char * start = s;

  while (*s >= '0' && *s <= '9') s++;
  if (*s == '\0')
  {
    mpz_set_str(i, start, 10);
  }
  else
  {
    char c = *s;
    *s = '\0';
    mpz_set_str(i, start, 10);
    *s = c;
  }
  return s;
}

static void fmpq_rat_init(fmpq_rat_ptr a, const coeffs r)
{
  fmpq_mpoly_init(a->num, r->data->ctx);
  fmpq_mpoly_init(a->den, r->data->ctx);
}

static void fmpq_rat_clear(fmpq_rat_ptr a, const coeffs r)
{
  fmpq_mpoly_clear(a->num, r->data->ctx);
  fmpq_mpoly_clear(a->den, r->data->ctx);
}

static void fmpq_rat_canonicalise(fmpq_rat_ptr a, const coeffs r)
{
  fmpz_t n, d;
  fmpz_init(n);
  fmpz_init(d);
  fmpz_gcd(n, fmpq_numref(a->num->content), fmpq_numref(a->den->content));
  fmpz_lcm(d, fmpq_denref(a->num->content), fmpq_denref(a->den->content));
  if (!fmpz_is_one(d))
  {
     fmpq_mul_fmpz(a->num->content, a->num->content, d);
     fmpq_mul_fmpq(a->den->content, a->den->content, d);
  }
  if (!fmpz_is_one(n))
  {
     fmpq_div_fmpz(a->num->content, a->num->content, n);
     fmpq_div_fmpz(a->den->content, a->den->content, n);
  }
  fmpz_clear(n);
  fmpz_clear(d);
}

/******************************************************************************
* Main interface
******************************************************************************/

static BOOLEAN CoeffIsEqual(const coeffs c, n_coeffType n, void * parameter)
{
  return (c->type == n);
}

static number Mult(number a, number b, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_equal(x->den, y->den, ctx) /* denominators equal */
  {
    fmpq_mpoly_mul(res->num, x->num, y->num, ctx);
    fmpq_mpoly_mul(res->den, x->den, y->den, ctx);
  } else if (fmpq_mpoly_is_one(x->den, ctx)) /* first denominator 1 */
  {
    fmpq_mpoly_t gd;
    fmpq_mpoly_init(gd, ctx);
    fmpz_mpoly_gcd(gd, x->num, y->den, ctx);
    if (fmpz_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, x->num, y->num, ctx);
      fmpq_mpoly_set(res->den, y->den, ctx);
    } else
    {
      fmpq_mpoly_div(res->num, x->num, gd, ctx);
      fmpq_mpoly_mul(res->num, res->num, y->num, ctx);
      fmpq_mpoly_div(res->den, y->den, gd, ctx);
    }
    fmpq_mpoly_clear(gd, ctx);
  } else if (fmpq_mpoly_is_one(y->den, ctx)) /* second denominator 1 */
  {
    fmpq_mpoly_t gd;
    fmpz_mpoly_init(gd, ctx);
    fmpz_mpoly_gcd(gd, y->num, x->den, ctx);
    if (fmpz_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, y->num, x->num, ctx);
      fmpq_mpoly_set(res->den, x->den, ctx);
    } else
    {
      fmpq_mpoly_div(res->num, y->num, gd, ctx);
      fmpq_mpoly_mul(res->num, res->num, x->num, ctx);
      fmpq_mpoly_div(res->den, x->den, gd, ctx);
    }
    fmpq_mpoly_clear(gd, ctx);							
  } else /* general case */
  {
    fmpq_mpoly_t g1, g2;
    fmpq_mpoly_ptr n1, n2, d1, d2;
    fmpq_mpoly_init(g1, ctx);
    fmpq_mpoly_init(g2, ctx);
    fmpq_mpoly_gcd(g1, x->num, y->den, ctx);
    fmpq_mpoly_gcd(g2, y->num, x->den, ctx);
    n1 = x->num; d2 = y->den;
    if (!fmpq_mpoly_is_one(g1, ctx))
    {
      fmpq_mpoly_div(res->num, x->num, g1, ctx);
      fmpq_mpoly_div(g1, y->den, g1, ctx);
      n1 = res->num; d2 = g1;
    }
    if (!fmpq_mpoly_is_one(g2, ctx))
    {
      fmpq_mpoly_div(res->den, y->num, g2, ctx);
      fmpq_mpoly_div(g2, x->den, g2, ctx);
      n2 = res->den; d1 = g2;
    }
    fmpq_mpoly_mul(res->num, n1, n2, ctx);
    fmpq_mpoly_mul(res->den, d1, d2, ctx);
    fmpq_mpoly_clear(g1, ctx);
    fmpq_mpoly_clear(g2, ctx);
  }
  return (number) res;
}

static number Sub(number a, number b, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_equal(x->den, y->den, ctx) /* denominators equal */
  {
    fmpq_mpoly_sub(res->num, x->num, y->num, ctx);
    if (fmpq_mpoly_is_one(x->den, ctx))
    {
      fmpq_mpoly_set(res->den, x->den, ctx);
    } else
    {
      fmpq_mpoly_t gd;
      fmpq_mpoly_init(gd, ctx);
      fmpq_mpoly_gcd(gd, res->num, x->den, ctx);
      if (fmpq_mpoly_is_one(gd, ctx))
      {
        fmpq_mpoly_set(res->den, x->den, ctx);
      } else
      {
        fmpq_mpoly_div(res->den, x->den, gd, ctx);
        fmpq_mpoly_div(res->num, res->num, gd, ctx);
      }
      fmpq_mpoly_clear(gd, ctx);
    } 
  } else if (fmpq_mpoly_is_one(x->den, ctx)) /* first denominator 1 */
  {
    fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
    fmpq_mpoly_sub(res->num, res->num, y->num, ctx);
    fmpq_mpoly_set(res->den, y->den, ctx);
  } else if (fmpq_mpoly_is_one(y->den, ctx)) /* second denominator 1 */
  {
    fmpq_mpoly_mul(res->num, y->num, x->den, ctx);
    fmpq_mpoly_sub(res->num, x->num, res->num, ctx);
    fmpq_mpoly_set(res->den, x->den, ctx);
  } else /* general case */
  {
    fmpq_mpoly_t gd;
    fmpq_mpoly_init(gd, ctx);
    fmpq_mpoly_gcd(gd, x->den, y->den, ctx);
    if (fmpq_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
      fmpq_mpoly_mul(gd, y->num, x->den, ctx);
      fmpq_mpoly_sub(res->num, res->num, gd, ctx);
      fmpq_mpoly_mul(res->den, x->den, y->den, ctx);
    } else
    {
      fmpq_mpoly_t q2;
      fmpq_mpoly_init(q2, ctx);
      fmpq_mpoly_div(res->den, x->den, gd, ctx);
      fmpq_mpoly_div(q2, y->den, gd, ctx);
      fmpq_mpoly_mul(res->num, q2, x->num, ctx);
      fmpq_mpoly_mul(res->den, res->den, y->num, ctx);
      fmpq_mpoly_sub(res->num, res->num, res->den, ctx);
      fmpq_mpoly_gcd(res->den, res->num, gd, ctx);
      if (fmpq_mpoly_is_one(res->den, ctx))
      {
        fmpq_mpoly_mul(res->den, q2, x->den, ctx);
      } else
      {
        fmpq_mpoly_div(res->num, res->num, res->den, ctx);
        fmpq_mpoly_div(gd, x->den, res->den, ctx);
        fmpq_mpoly_mul(res->den, gd, q2, ctx);
      }
      fmpq_mpoly_clear(q2);
    }
    fmpq_mpoly_clear(gd, ctx);
  }
  return (number) res;
}

static number Add(number a, number b, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_equal(x->den, y->den, ctx) /* denominators equal */
  {
    fmpq_mpoly_add(res->num, x->num, y->num, ctx);
    if (fmpq_mpoly_is_one(x->den, ctx))
    {
      fmpq_mpoly_set(res->den, x->den, ctx);
    } else
    {
      fmpq_mpoly_t gd;
      fmpq_mpoly_init(gd, ctx);
      fmpq_mpoly_gcd(gd, res->num, x->den, ctx);
      if (fmpq_mpoly_is_one(gd, ctx))
      {
        fmpq_mpoly_set(res->den, x->den, ctx);
      } else
      {
        fmpq_mpoly_div(res->den, x->den, gd, ctx);
        fmpq_mpoly_div(res->num, res->num, gd, ctx);
      }
      fmpq_mpoly_clear(gd, ctx);
    }
  } else if (fmpq_mpoly_is_one(x->den, ctx)) /* first denominator 1 */
  {
    fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
    fmpq_mpoly_add(res->num, res->num, y->num, ctx);
    fmpq_mpoly_set(res->den, y->den, ctx);
  } else if (fmpq_mpoly_is_one(y->den, ctx)) /* second denominator 1 */
  {
    fmpq_mpoly_mul(res->num, y->num, x->den, ctx);
    fmpq_mpoly_add(res->num, x->num, res->num, ctx);
    fmpq_mpoly_set(res->den, x->den, ctx);
  } else /* general case */
  {
    fmpq_mpoly_t gd;
    fmpq_mpoly_init(gd, ctx);
    fmpq_mpoly_gcd(gd, x->den, y->den, ctx);
    if (fmpq_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
      fmpq_mpoly_mul(gd, y->num, x->den, ctx);
      fmpq_mpoly_add(res->num, res->num, gd, ctx);
      fmpq_mpoly_mul(res->den, x->den, y->den, ctx);
    } else
    {
      fmpq_mpoly_t q2;
      fmpq_mpoly_init(q2, ctx);
      fmpq_mpoly_div(res->den, x->den, gd, ctx);
      fmpq_mpoly_div(q2, y->den, gd, ctx);
      fmpq_mpoly_mul(res->num, q2, x->num, ctx);
      fmpq_mpoly_mul(res->den, res->den, y->num, ctx);
      fmpq_mpoly_add(res->num, res->num, res->den, ctx);
      fmpq_mpoly_gcd(res->den, res->num, gd, ctx);
      if (fmpq_mpoly_is_one(res->den, ctx))
      {
        fmpq_mpoly_mul(res->den, q2, x->den, ctx);
      } else
      {
        fmpq_mpoly_div(res->num, res->num, res->den, ctx);
        fmpq_mpoly_div(gd, x->den, res->den, ctx);
        fmpq_mpoly_mul(res->den, gd, q2, ctx);
      }
      fmpq_mpoly_clear(q2);
    }
    fmpq_mpoly_clear(gd, ctx);
  }
  return (number) res;
}

static number Div(number a, number b, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_is_zero(y->num, ctx))
  {
    WerrorS(nDivBy0);
    return NULL; 
  }
  fmpq_rat_init(res, c);
  if (fmpq_mpoly_equal(x->den, y->num, ctx) /* denominators equal */
  {
    fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
    fmpq_mpoly_mul(res->den, x->den, y->num, ctx);
  } else if (fmpq_mpoly_is_one(x->den, ctx)) /* first denominator 1 */
  {
    fmpq_mpoly_t gd;
    fmpq_mpoly_init(gd, ctx);
    fmpz_mpoly_gcd(gd, x->num, y->num, ctx);
    if (fmpz_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, x->num, y->den, ctx);
      fmpq_mpoly_set(res->den, y->num, ctx);
    } else
    {
      fmpq_mpoly_div(res->num, x->num, gd, ctx);
      fmpq_mpoly_mul(res->num, res->num, y->den, ctx);
      fmpq_mpoly_div(res->den, y->num, gd, ctx);
    }
    fmpq_mpoly_clear(gd, ctx);
  } else if (fmpq_mpoly_is_one(y->num, ctx)) /* second denominator 1 */
  {
    fmpq_mpoly_t gd;
    fmpz_mpoly_init(gd, ctx);
    fmpz_mpoly_gcd(gd, y->den, x->den, ctx);
    if (fmpz_mpoly_is_one(gd, ctx))
    {
      fmpq_mpoly_mul(res->num, y->den, x->num, ctx);
      fmpq_mpoly_set(res->den, x->den, ctx);
    } else
    {
      fmpq_mpoly_div(res->num, y->den, gd, ctx);
      fmpq_mpoly_mul(res->num, res->num, x->num, ctx);
      fmpq_mpoly_div(res->den, x->den, gd, ctx);
    }
    fmpq_mpoly_clear(gd, ctx);
  } else /* general case */
  {
    fmpq_mpoly_t g1, g2;
    fmpq_mpoly_ptr n1, n2, d1, d2;
    fmpq_mpoly_init(g1, ctx);
    fmpq_mpoly_init(g2, ctx);
    fmpq_mpoly_gcd(g1, x->num, y->num, ctx);
    fmpq_mpoly_gcd(g2, y->den, x->den, ctx);
    n1 = x->num; d2 = y->num;
    if (!fmpq_mpoly_is_one(g1, ctx))
    {
      fmpq_mpoly_div(res->num, x->num, g1, ctx);
      fmpq_mpoly_div(g1, y->num, g1, ctx);
      n1 = res->num; d2 = g1;
    }
    if (!fmpq_mpoly_is_one(g2, ctx))
    {
      fmpq_mpoly_div(res->den, y->den, g2, ctx);
      fmpq_mpoly_div(g2, x->den, g2, ctx);
      n2 = res->den; d1 = g2;
    }
    fmpq_mpoly_mul(res->num, n1, n2, ctx);
    fmpq_mpoly_mul(res->den, d1, d2, ctx);
    fmpq_mpoly_clear(g1, ctx);
    fmpq_mpoly_clear(g2, ctx);
  }
  return (number) res;
}

static number ExactDiv(number a, number b, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  if (fmpq_mpoly_is_zero(y->num, ctx)
  {
     WerrorS(nDivBy0);
     return NULL;
  }
  fmpq_rat_init(res, c);
  fmpq_mpoly_div(res->num, x->num, y->num, ctx);
  return (number) res;
}

// static number IntMod(number a, number b, const coeffs c);
// {
// }

static number Init(long i, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_set_si(res->num, (slong) i);
  fmpq_mpoly_set_si(res->den, (slong) 1);
  return (number) res;
}

static number InitMPZ(mpz_t i, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_set_mpz(res->num, i);
  fmpq_mpoly_set_si(res->den, (slong) 1);
  return (number) res;
}

static int Size(number n, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) n;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_is_zero(x->num, ctx))
    return 0;
  return fmpq_mpoly_length(x->num, ctx) +
         fmpq_mpoly_length(x->den, ctx);
}

static long Int(number &n, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) n;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_is_fmpq(x->den, ctx) && fmpq_mpoly_is_fmpq(x->num, ctx))
  {
    long nl = 0;
    fmpq_t r;
    fmpq_init(r);
    fmpq_div(r, x->num->content, x->den->content);
    if (fmpz_is_one(fmpq_denref(r)))
    {
      if (fmpz_fits_si(fmpq_numref(r)))
        nl = fmpz_get_si(fmpq_numref(r));
    }
    fmpq_clear(r);
    return nl;
  }
  return 0;
}

static void MPZ(mpz_t result, number &n, const coeffs c)
{
  mpz_init(result);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) n;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_is_fmpq(x->den, ctx) && fmpq_mpoly_is_fmpq(x->num, ctx))
  {
    long nl = 0;
    fmpq_t r;
    fmpq_init(r);
    fmpq_div(r, x->num->content, x->den->content);
    if (fmpz_is_one(fmpq_denref(r)))
    {
      fmpz_set(result, fmpq_numref(r));
    }
    fmpq_clear(r);
  }
}

static number Neg(number a, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_poly_neg(x->num, x->num, ctx);
  return a;
}

static number Invers(number a, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (fmpq_mpoly_is_zero(x->num)
  {
    WerrorS(nDivBy0);
    return NULL;
  } else
  {
    fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
    fmpq_rat_init(res, c);
    fmpq_mpoly_set(res->num, x->den, ctx);
    fmpq_mpoly_set(res->den, x->num, ctx);
    return (number) res;
  }
}

static number Copy(number a, const coeffs c)
{
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_mpoly_set(res->num, x->num, ctx);
  fmpq_mpoly_set(res->den, x->den, ctx);
  return (number) res;
}

//static number RePart(number a, const coeffs c)
//{
//}

//static number ImPart(number a, const coeffs c)
//{
//}

static BOOLEAN IsOne(number a, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (!fmpq_mpoly_is_fmpq(x->num, ctx))
    return FALSE;
  if (!fmpq_mpoly_is_fmpq(x->den, ctx))
    return FALSE;
  return fmpq_equal(x->num->content, x->den->content);
}

static BOOLEAN IsZero(number a, const coeffs c);
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  return fmpq_mpoly_is_zero(x->num, ctx);
}

static void WriteLong(number &a, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpz_t t;
  char *s;
  long int i, j, k, nmax_i, dmax_i, max_digits;
  fmpq_rat_canonicalise(x);
  if (fmpq_mpoly_is_zero(x->num, ctx))
    StringAppendS("0");
  else
  {
    BOOLEAN num_is_const = fmpq_mpoly_is_fmpq(x->num, ctx);
    BOOLEAN need_times;
    fmpz_mpoly_struct * znum = x->num->zpoly;
    fmpz_mpoly_struct * zden = x->den->zpoly;
    slong nvars = fmpq_mpoly_ctx_nvars(ctx);
    fmpz_init(t);
    nmax_i = 0;
    dmax_i = 0;
    for (i = 1; i < fmpz_mpoly_length(znum, ctx); i++)
    {
      if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(znum, i, ctx),
                      fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx)) > 0)
      {
         nmax_i = i;
      }
    }
    for (i = 1; i < fmpz_mpoly_length(zden, ctx); i++)
    {
      if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(zden, i, ctx),
                      fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx)) > 0)
      {
        dmax_i = i;
      }
    }
    if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx),
                       fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx)) > 0)
    {
      fmpz_mul(t, fmpq_numref(x->num->content),
                  fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx));       
      max_digits = fmpz_sizeinbase(t, 10);
    } else
    {
      fmpz_mul(t, fmpq_numref(x->den->content),
                  fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx));
      max_digits = fmpz_sizeinbase(t, 10);
    }
    s = (char*) omAlloc(max_digits + 2);
    if (!num_is_const)
      StringAppendS("(");
    if (fmpq_mpoly_is_one(x->num, ctx))
      StringAppendS("1");
    else
    {
      for (i = 0; i < fmpq_mpoly_length(x->num, ctx); i++)
      {
        need_times = TRUE;
        fmpz_mul(t, fmpz_mpoly_get_coeff_fmpz_ref(znum, i, ctx),
                                       fmpq_numref(x->num->content));
        if (i != 0 && fmpz_sgn(t) > 0)
          StringAppendS("+");
        if (!fmpz_is_one(t))
        {
          fmpz_get_str(s, 10, t);
        } else
        {
          need_times = FALSE;
        }
        StringAppendS(z);
        for (j = 0; j < nvars; j++)
        {
          k = fmpq_mpoly_get_term_var_exp_ui(expt, x->num, i, j, ctx);
          if (k != 0)
          {
            if (need_times)
              StringAppendS("*")
            if (k != 1)
              StringAppend("%s^%d", c->pParameterNames[j], k);
            else
              StringAppend("%s", c->pParameterNames[j]);
            need_times = TRUE;
          }
        }
      }
    }
    if (!num_isconst)
       StringAppendS(")");
    if (!fmpq_mpoly_is_one(x->den, ctx))
    {
      StringAppendS("/");
      if (!den_isconst)
        StringAppendS("(");
      for (i = 0; i < fmpq_mpoly_length(x->den, ctx); i++)
      {
        need_times = TRUE;
        fmpz_mul(t, fmpz_mpoly_get_coeff_fmpz_ref(zden, i, ctx),
                                       fmpq_numref(x->den->content));
        if (i != 0 && fmpz_sgn(t) > 0)
          StringAppendS("+");
        if (!fmpz_is_one(t))
        {
          fmpz_get_str(s, 10, t);
          StringAppendS(z);
        } else
        {
          need_times = FALSE;
        }
        for (j = 0; j < nvars; j++)
        {
          k = fmpq_mpoly_get_term_var_exp_ui(expt, x->num, i, j, ctx);
          if (k != 0)
          {
            if (need_times)
              StringAppendS("*");
            if (k != 1)
              StringAppend("%s^%d", c->pParameterNames[j], k);
            else
              StringAppend("%s", c->pParameterNames[j]);
            need_times = TRUE;
          }
        }
      }      
      if (!den_isconst)
        StringAppendS(")");
    }
    fmpz_clear(t);
  }
}

static void WriteShort(number a, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpz_t t;
  char *s;
  long int i, j, k, nmax_i, dmax_i, max_digits;
  fmpq_rat_canonicalise(x);
  if (fmpq_mpoly_is_zero(x->num, ctx))
    StringAppendS("0");
  else
  {
    BOOLEAN num_is_const = fmpq_mpoly_is_fmpq(x->num, ctx);
    fmpz_mpoly_struct * znum = x->num->zpoly;
    fmpz_mpoly_struct * zden = x->den->zpoly;
    slong nvars = fmpq_mpoly_ctx_nvars(ctx);
    fmpz_init(t);
    nmax_i = 0;
    dmax_i = 0;
    for (i = 1; i < fmpz_mpoly_length(znum, ctx); i++)
    {
      if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(znum, i, ctx),
                      fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx)) > 0)
      {
         nmax_i = i;
      }
    }
    for (i = 1; i < fmpz_mpoly_length(zden, ctx); i++)
    {
      if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(zden, i, ctx),
                      fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx)) > 0)
      {
        dmax_i = i;
      }
    }
    if (fmpz_cmpabs(fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx),
                       fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx)) > 0)
    {
      fmpz_mul(t, fmpq_numref(x->num->content),
                  fmpz_mpoly_get_coeff_fmpz_ref(znum, nmax_i, ctx));       
      max_digits = fmpz_sizeinbase(t, 10);
    } else
    {
      fmpz_mul(t, fmpq_numref(x->den->content),
                  fmpz_mpoly_get_coeff_fmpz_ref(zden, dmax_i, ctx));
      max_digits = fmpz_sizeinbase(t, 10);
    }
    s = (char*) omAlloc(max_digits + 2);
    if (!num_is_const)
      StringAppendS("(");
    if (fmpq_mpoly_is_one(x->num, ctx))
      StringAppendS("1");
    else
    {
      for (i = 0; i < fmpq_mpoly_length(x->num, ctx); i++)
      {
        fmpz_mul(t, fmpz_mpoly_get_coeff_fmpz_ref(znum, i, ctx),
                                       fmpq_numref(x->num->content));
        if (i != 0 && fmpz_sgn(t) > 0)
          StringAppendS("+");
        if (!fmpz_is_one(t))
        {
          fmpz_get_str(s, 10, t);
        }
        StringAppendS(z);
        for (j = 0; j < nvars; j++)
        {
          k = fmpq_mpoly_get_term_var_exp_ui(expt, x->num, i, j, ctx);
          if (k != 0)
          {
            if (k != 1)
              StringAppend("%s%d", c->pParameterNames[j], k);
            else
              StringAppend("%s", c->pParameterNames[j]);
          }
        }
      }
    }
    if (!num_isconst)
       StringAppendS(")");
    if (!fmpq_mpoly_is_one(x->den, ctx))
    {
      StringAppendS("/");
      if (!den_isconst)
        StringAppendS("(");
      for (i = 0; i < fmpq_mpoly_length(x->den, ctx); i++)
      {
        fmpz_mul(t, fmpz_mpoly_get_coeff_fmpz_ref(zden, i, ctx),
                                       fmpq_numref(x->den->content));
        if (i != 0 && fmpz_sgn(t) > 0)
          StringAppendS("+");
        if (!fmpz_is_one(t))
        {
          fmpz_get_str(s, 10, t);
          StringAppendS(z);
        }
        for (j = 0; j < nvars; j++)
        {
          k = fmpq_mpoly_get_term_var_exp_ui(expt, x->num, i, j, ctx);
          if (k != 0)
          {
            if (k != 1)
              StringAppend("%s%d", c->pParameterNames[j], k);
            else
              StringAppend("%s", c->pParameterNames[j]);
          }
        }
      }      
      if (!den_isconst)
        StringAppendS(")");
    }
    fmpz_clear(t);
  }
}

static const char* Read(const char * st, number * a, const coeffs c)
{
  // we only read "monomials" (i.e. [-][digits][parameter]),
  // everything else (+,*,^,()) is left to the singular interpreter
  char *s = (char *) st;
  *a = (number) omAlloc(sizeof(fmpq_poly_t));
  fmpq_poly_init((fmpq_poly_ptr)(*a));
  BOOLEAN neg = FALSE;
  if (*s=='-')
  {
    neg = TRUE;
    s++;
  }
  if (isdigit(*s))
  {
    mpz_t z;
    mpz_init(z);
    s=nlEatLong((char *) s, z);
    fmpq_poly_set_mpz((fmpq_poly_ptr)(*a),z);
    if (*s == '/')
    {
      s++;
      s=nlEatLong((char *) s, z);
      fmpq_poly_scalar_div_mpz((fmpq_poly_ptr)(*a),(fmpq_poly_ptr)(*a),z);
    }
    mpz_clear(z);
  }
  else if (strncmp(s, c->pParameterNames[0], strlen(c->pParameterNames[0])) == 0)
  {
    fmpq_poly_set_coeff_si((fmpq_poly_ptr)(*a), 1, 1);
    s += strlen(c->pParameterNames[0]);
    if(isdigit(*s))
    {
      int i = 1;
      s=nEati(s, &i, 0);
      if (i != 1)
      {
        fmpq_poly_set_coeff_si((fmpq_poly_ptr)(*a), 1, 0);
        fmpq_poly_set_coeff_si((fmpq_poly_ptr)(*a), i, 1);
      }
    }
  }
  if (neg)
    fmpq_poly_neg((fmpq_poly_ptr)(*a), (fmpq_poly_ptr)(*a));
  return s;
}

static void Normalize(number &a, const coeffs c)
{
  /* everything already normalized */
}

static BOOLEAN Greater(number a, number b, const coeffs c)
{
  return Size(a, c) > Size(b, c);
}

static BOOLEAN Equal(number a, number b, const coeffs c)
{
  fmpz_t t1, t2;
  int eq;
  const fmpq_mpoly_ptr x = (fmpq_mpoly_ptr) a;
  const fmpq_mpoly_ptr y = (fmpq_mpoly_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (!fmpz_mpoly_equal(x->num->zpoly, y->num->zpoly, ctx->zctx))
    return FALSE;
  if (!fmpz_mpoly_equal(x->den->zpoly, y->den->zpoly, ctx->zctx))
    return FALSE;
  fmpz_init(t1);
  fmpz_init(t2);
  fmpz_mul(t1, fmpq_numref(x->num->content), fmpq_numref(x->den->content));
  fmpz_mul(t1, t1, fmpq_denref(y->num->content));
  fmpz_mul(t1, t1, fmpq_denref(y->den->content));
  fmpz_mul(t2, fmpq_numref(y->num->content), fmpq_numref(y->den->content));
  fmpz_mul(t2, t2, fmpq_denref(x->num->content));
  fmpz_mul(t2, t2, fmpq_denref(x->den->content));
  eq = fmpz_equal(t1, t2);
  fmpz_clear(t1);
  fmpz_clear(t2);
  return eq;
}

static BOOLEAN IsMOne(number a, const coeffs c)
{
  int eq;
  fmpq_t content;
  const fmpq_mpoly_ptr x = (fmpq_mpoly_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  if (!fmpq_mpoly_is_fmpq(x->num, ctx))
    return FALSE;
  if (!fmpq_mpoly_is_fmpq(x->den, ctx))
    return FALSE;
  fmpq_init(content);
  fmpq_neg(content, x->num->content);
  eq = fmpq_equal(content, x->den->content);
  fmpq_clear(content);
  return eq;
}

static BOOLEAN GreaterZero(number k, const coeffs c)
{
  return TRUE; /* everything in parens for now so need + sign */
}

static void Power(number a, int i, number * result, const coeffs c)
{
  fmpq_rat_init((fmpq_rat_ptr) result, c);
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_mpoly_pow_si((*result)->num, x->num, (slong) i, ctx);
  fmpq_mpoly_pow_si((*result)->den, x->den, (slong) i, ctx);
}

static number GetDenom(number &n, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) n;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_set(res->num, x->den, ctx);
  fmpq_mpoly_one(res->den, ctx);
  return (number) res;
}

static number GetNumerator(number &n, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) n;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_set(res->num, x->num, ctx);
  fmpq_mpoly_one(res->den, ctx);
  return (number) res;
}

static number Gcd(number a, number b, const coeffs c)
{
  const fmpq_rat_ptr x = (fmpq_rat_ptr) a;
  const fmpq_rat_ptr y = (fmpq_rat_ptr) b;
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_one(res->den, ctx);
  return (number) res;
}

static number ExtGcd(number a, number b, number *s, number *t, const coeffs c)
{
  WerrorS("not a Euclidean ring: ExtGcd");
}

static number Lcm(number a, number b, const coeffs c)
{
  WerrorS("not yet: Lcm");
}

static void Delete(number * a, const coeffs c)
{
  if ((*a) != NULL)
  {
    const fmpq_rat_ptr x = (fmpq_rat_ptr) *a;
    fmpq_rat_clear(x);
    omFree(*a);
    *a = NULL;
  }
}

static nMapFunc SetMap(const coeffs src, const coeffs dst)
{
  WerrorS("not yet: SetMap");
  return NULL;
}

//static void InpMult(number &a, number b, const coeffs c)
//{
//}

//static void InpAdd(number &a, number b, const coeffs c)
//{
//}

static number Init_bigint(number i, const coeffs dummy, const coeffs dst)
{
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) dst->data->ctx;
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpz_t f;
  fmpq_rat_init(res, dst);
  if (SR_HDL(i) & SR_INT)
  {
    fmpq_mpoly_set_si(res, SR_TO_INT(i), ctx);
  }
  else
  {
    fmpz_init(f);
    fmpz_set_mpz(f, i->z);
    fmpq_mpoly_set_fmpz(res, f);
    fmpz_clear(f);
  }
  return (number) res;
}

static number Farey(number p, number n, const coeffs c)
{
  WerrorS("not yet: Farey");
}

static number ChineseRemainder(number *x, number *q, int rl,
                    BOOLEAN sym, CFArray &inv_cache, const coeffs c)
{
  WerrorS("not yet: ChineseRemainder");
}

static int ParDeg(number a, const coeffs c)
{
    const fmpq_mpoly_ptr x = (fmpq_mpoly_ptr) a;
    const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
    return (int) (fmpq_mpoly_total_degree(x->num, ctx) - 
		  fmpq_mpoly_total_degree(x->den, ctx));
}

static number Parameter(const int i, const coeffs c)
{
  const fmpq_ctx_ptr ctx = (fmpq_ctx_ptr) c->data->ctx;
  fmpq_rat_ptr res = (fmpq_rat_ptr) omAlloc(sizeof(fmpq_rat_struct));
  fmpq_rat_init(res, c);
  fmpq_mpoly_gen(res->num, (slong) i, ctx);
  fmpq_mpoly_one(res->den, ctx);
  return (number) res;
}

static void WriteFd(number a, const ssiInfo *d, const coeffs c)
{
  // format: len a_len(num den) .. a_0
  fmpq_poly_ptr aa = (fmpq_poly_ptr) a;
  int l = fmpq_poly_length(aa);
  fprintf(d->f_write, "%d ", l);
  mpq_t m;
  mpq_init(m);
  mpz_t num, den;
  mpz_init(num);
  mpz_init(den);
  for(int i = l; i >= 0; i--)
  {
    fmpq_poly_get_coeff_mpq(m, (fmpq_poly_ptr)a, i);
    mpq_get_num(num, m);
    mpq_get_den(den, m);
    mpz_out_str(d->f_write, SSI_BASE, num);
    fputc(' ', d->f_write);
    mpz_out_str(d->f_write, SSI_BASE, den);
    fputc(' ', d->f_write);
  }
  mpz_clear(den);
  mpz_clear(num);
  mpq_clear(m);
}

static number ReadFd(const ssiInfo *d, const coeffs c)
{
  // format: len a_len .. a_0
  fmpq_poly_ptr aa = (fmpq_poly_ptr) omAlloc(sizeof(fmpq_poly_t));
  fmpq_poly_init(aa);
  int l = s_readint(d->f_read);
  mpz_t nm;
  mpz_init(nm);
  mpq_t m;
  mpq_init(m);
  for (int i = l; i >= 0; i--)
  {
    s_readmpz_base(d->f_read, nm, SSI_BASE);
    mpq_set_num(m, nm);
    s_readmpz_base(d->f_read, nm, SSI_BASE);
    mpq_set_den(m, nm);
    fmpq_poly_set_coeff_mpq(aa, i, m);
  }
  mpz_clear(nm);
  mpq_clear(m);
  return (number)aa;
}

// cfClearContent

// cfClearDenominators

static number ConvFactoryNSingN(const CanonicalForm n, const coeffs c)
{
  WerrorS("not yet: ConvFactoryNSingN");
}

static CanonicalForm ConvSingNFactoryN(number n, BOOLEAN setChar, const coeffs c)
{
  WerrorS("not yet: ConvSingNFactoryN");
}

char * CoeffName(const coeffs c)
{
  STATIC_VAR char CoeffName_flint_Q[20];
  sprintf(CoeffName_flint_Q, "flint:QQ[%s]", c->pParameterNames[0]);
  return (char*) CoeffName_flint_Q;

}

static char* CoeffString(const coeffs c)
{
  char *buf = (char*) omAlloc(12 + strlen(c->pParameterNames[0]));
  sprintf(buf, "flintQ(\"%s\")", c->pParameterNames[0]);
  return buf;
}

static void CoeffWrite(const coeffs c, BOOLEAN details)
{
  PrintS(CoeffName(c));
}

coeffs flintQInitCfByName(char *s, n_coeffType n)
{
  const char start[] = "flint:QQ[";
  const int start_len = strlen(start);
  if (strncmp(s, start, start_len) == 0)
  {
    s += start_len;
    char st[10];
    int l = sscanf(s, "%s", st);
    if (l == 1)
    {
      while (st[strlen(st) - 1] == ']')
        st[strlen(st) - 1] = '\0';
      return nInitChar(n, (void*) st);
    }
  }
  return NULL;
}

#ifdef LDEBUG
static BOOLEAN DBTest(number a, const char *f, const int l, const coeffs c)
{
  return TRUE;
}

#endif
static void KillChar(coeffs cf)
{
  omFree((ADDRESS)(cf->pParameterNames[0]));
  omFreeSize(cf->pParameterNames,sizeof(char*));
}

BOOLEAN flintQ_InitChar(coeffs cf, void * infoStruct)
{
  char *pp=(char*)infoStruct;
  cf->cfCoeffString  = CoeffString;
  cf->cfCoeffName    = CoeffName;
  cf->cfCoeffWrite   = CoeffWrite;
  cf->nCoeffIsEqual  = CoeffIsEqual;
  cf->cfKillChar     = KillChar;
  cf->cfSetChar      = SetChar;
  cf->ch             = 0; //char 0
  cf->cfMult         = Mult;
  cf->cfSub          = Sub;
  cf->cfAdd          = Add;
  cf->cfDiv          = Div;
  cf->cfExactDiv     = ExactDiv; // ???
  cf->cfInit         = Init;
  cf->cfInitMPZ      = InitMPZ;
  cf->cfSize         = Size;
  cf->cfInt          = Int;
  cf->cfMPZ          = MPZ;
  cf->cfInpNeg       = Neg;
  cf->cfInvers       = Invers;
  cf->cfCopy         = Copy;
  cf->cfRePart       = Copy;
  // default: cf->cfImPart       = ndReturn0;
  cf->cfWriteLong    = WriteLong;
  cf->cfWriteShort   = WriteShort;
  cf->cfRead         = Read;
  cf->cfNormalize    = Normalize;

  //cf->cfDivComp=
  //cf->cfIsUnit=
  //cf->cfGetUnit=
  //cf->cfDivBy=

  cf->cfGreater      = Greater;
  cf->cfEqual        = Equal;
  cf->cfIsZero       = IsZero;
  cf->cfIsOne        = IsOne;
  cf->cfIsMOne       = IsMOne;
  cf->cfGreaterZero  = GreaterZero;

  cf->cfPower        = Power;
  cf->cfGetDenom     = GetDenom;
  cf->cfGetNumerator = GetNumerator;
  cf->cfGcd          = Gcd;
  cf->cfExtGcd       = ExtGcd;
  cf->cfLcm          = Lcm;
  cf->cfDelete       = Delete;
  cf->cfSetMap       = SetMap;
  // default: cf->cfInpMult
  // default: cf->cfInpAdd
  cf->cfFarey        =Farey;
  cf->cfChineseRemainder = ChineseRemainder;
  cf->cfParDeg       = ParDeg;
  cf->cfParameter    = Parameter;
  //  cf->cfClearContent = ClearContent;
  //  cf->cfClearDenominators = ClearDenominators;
  cf->convFactoryNSingN = ConvFactoryNSingN;
  cf->convSingNFactoryN = ConvSingNFactoryN;
  cf->cfWriteFd      = WriteFd;
  cf->cfReadFd       = ReadFd;
#ifdef LDEBUG
  cf->cfDBTest       = DBTest;
#endif

  cf->iNumberOfParameters = 1;
  char **pn = (char**) omAlloc0(sizeof(char*));
  pn[0] = omStrDup(pp);
  cf->pParameterNames = (const char **) pn;
  cf->has_simple_Inverse = FALSE;
  cf->has_simple_Alloc = FALSE;
  cf->is_field = FALSE;

  return FALSE;
}
#endif
