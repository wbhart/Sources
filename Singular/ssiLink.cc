/****************************************
 * Computer Algebra System SINGULAR     *
 ****************************************/
/***************************************************************
 * File:    ssiLink.h
 *  Purpose: declaration of sl_link routines for ssi
 *  Version: $Id$
 ***************************************************************/
#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include <signal.h>
#include <sys/select.h>
#include <ctype.h>   /*for isdigit*/


#include "mod2.h"

#include "tok.h"
#include "ipid.h"
#include <omalloc.h>
#include <kernel/ring.h>
#include <kernel/matpol.h>
#include <kernel/ideals.h>
#include <kernel/polys.h>
#include <kernel/longrat.h>
#include <kernel/ideals.h>
#include "subexpr.h"
#include "silink.h"
#include "lists.h"
#include "ssiLink.h"

typedef struct
{
  FILE *f_read;
  FILE *f_write;
  ring r;
  pid_t pid; /* only valid for fork/tcp mode*/
  int fd_read,fd_write; /* only valid for fork/tcp mode*/
  char level;
} ssiInfo;

// the helper functions:
void ssiSetCurrRing(const ring r)
{
  if (!rEqual(r,currRing,1))
  {
    char name[20];
    int nr=0;
    do
    { sprintf(name,"ssiRing%d",nr); nr++; }
    while(IDROOT->get(name, 0)!=NULL);
    idhdl h=enterid(omStrDup(name),0,RING_CMD,&IDROOT,FALSE);
    IDRING(h)=r;
    r->ref++;
    rSetHdl(h);
  }
}
// the implementation of the functions:
void ssiWriteInt(ssiInfo *d,const int i)
{
  fprintf(d->f_write,"%d ",i);
  //if (d->f_debug!=NULL) fprintf(d->f_debug,"int: %d ",i);
}

void ssiWriteString(ssiInfo *d,const char *s)
{
  fprintf(d->f_write,"%d %s ",strlen(s),s);
  //if (d->f_debug!=NULL) fprintf(d->f_debug,"stringi: %d \"%s\" ",strlen(s),s);
}


void ssiWriteBigInt(const ssiInfo *d, const number n)
{
  // syntax is as follows:
  // case 2 Q:     3 4 <int>
  //        or     3 3 <mpz_t nominator>
  if(SR_HDL(n) & SR_INT)
  {
    fprintf(d->f_write,"4 %ld ",SR_TO_INT(n));
    //if (d->f_debug!=NULL) fprintf(d->f_debug,"bigint: short \"%ld\" ",SR_TO_INT(n));
  }
  else if (n->s==3)
  {
    gmp_fprintf(d->f_write,"3 %Zd ",n->z);
    //if (d->f_debug!=NULL) gmp_fprintf(d->f_debug,"bigint: gmp \"%Zd\" ",n->z);
  }
  else Werror("illiegal bigint");
}

void ssiWriteNumber(const ssiInfo *d, const number n)
{
  // syntax is as follows:
  // case 1 Z/p:   3 <int>
  // case 2 Q:     3 4 <int>
  //        or     3 0 <mpz_t nominator> <mpz_t denominator>
  //        or     3 1  dto.
  //        or     3 3 <mpz_t nominator>
  if(rField_is_Zp(d->r))
  {
    fprintf(d->f_write,"%d ",(int)(long)n);
    //if (d->f_debug!=NULL) fprintf(d->f_debug,"number: \"%ld\" ",(int)(long)n);
  }
  else if (rField_is_Q(d->r))
  {
    if(SR_HDL(n) & SR_INT)
    {
      fprintf(d->f_write,"4 %ld ",SR_TO_INT(n));
      //if (d->f_debug!=NULL) fprintf(d->f_debug,"number: short \"%ld\" ",SR_TO_INT(n));
    }
    else if (n->s<2)
    {
      gmp_fprintf(d->f_write,"%d %Zd %Zd ",n->s,n->z,n->n);
      //if (d->f_debug!=NULL) gmp_fprintf(d->f_debug,"number: s=%d gmp/gmp \"%Zd %Zd\" ",n->s,n->z,n->n);
    }
    else /*n->s==3*/
    {
      gmp_fprintf(d->f_write,"3 %Zd ",n->z);
      //if (d->f_debug!=NULL) gmp_fprintf(d->f_debug,"number: gmp \"%Zd\" ",n->z);
    }
  }
  else WerrorS("coeff field not implemented");
}

void ssiWriteRing(ssiInfo *d,const ring r)
{
  /* 5 <ch> <N> <l1> <s1>....<ln> <sN> */
  if (d->r!=NULL) rKill(d->r);
  d->r=r;
  d->r->ref++;
  fprintf(d->f_write,"%d %d ",r->ch,r->N);

  int i;
  for(i=0;i<r->N;i++)
  {
    fprintf(d->f_write,"%d %s ",strlen(r->names[i]),r->names[i]);
  }
  /* number of orderings:*/
  i=0;
  while (r->order[i]!=0) i++;
  fprintf(d->f_write,"%d ",i);
  /* each ordering block: */
  i=0;
  while(r->order[i]!=0)
  {
    fprintf(d->f_write,"%d %d %d ",r->order[i],r->block0[i], r->block1[i]);
    i++;
  }
}

void ssiWritePoly(ssiInfo *d, int typ, poly p)
{
  fprintf(d->f_write,"%d ",pLength(p));//number of terms
  int i;

  while(p!=NULL)
  {
    ssiWriteNumber(d,pGetCoeff(p));
    //nWrite(fich,pGetCoeff(p));
    fprintf(d->f_write,"%ld ",p_GetComp(p,d->r));//component

    for(int j=1;j<=rVar(d->r);j++)
    {
      fprintf(d->f_write,"%ld ",p_GetExp(p,j,d->r ));//x^j
    }
    pIter(p);
  }
}

void ssiWriteIdeal(ssiInfo *d, int typ,ideal I)
{
   // syntax: 7 # of elements <poly 1> <poly2>.....
   // syntax: 8 <rows> <cols> <poly 1> <poly2>.....
   matrix M=(matrix)I;
   if (typ==MATRIX_CMD)
        fprintf(d->f_write,"%d %d ", MATROWS(M),MATCOLS(M));
   else
     fprintf(d->f_write,"%d ",IDELEMS(I));

   int i;
   int tt;
   if (typ==MODUL_CMD) tt=VECTOR_CMD;
   else                tt=POLY_CMD;

   for(i=0;i<IDELEMS(I);i++)
   {
     ssiWritePoly(d,tt,I->m[i]);
   }
}
void ssiWriteCommand(si_link l, command D)
{
  ssiInfo *d=(ssiInfo*)l->data;
  // syntax: <num ops> <operation> <op1> <op2> ....
  fprintf(d->f_write,"%d %d ",D->argc,D->op);
  if (D->argc >0) ssiWrite(l, &(D->arg1));
  if (D->argc < 4)
  {
    if (D->argc >1) ssiWrite(l, &(D->arg2));
    if (D->argc >2) ssiWrite(l, &(D->arg3));
  }
}

void ssiWriteProc(ssiInfo *d,procinfov p)
{
  ssiWriteString(d,p->data.s.body);
}

void ssiWriteList(si_link l,lists dd)
{
  ssiInfo *d=(ssiInfo*)l->data;
  fprintf(d->f_write,"%d ",dd->nr+1);
  int i;
  for(i=0;i<=dd->nr;i++)
  {
    ssiWrite(l,&(dd->m[i]));
  }
}

char *ssiReadString(ssiInfo *d)
{
  char *buf;
  int l;
  fscanf(d->f_read,"%d ",&l);
  buf=(char*)omAlloc(l+1);
  fread(buf,1,l,d->f_read);
  buf[l]='\0';
  return buf;
}

int ssiReadInt(FILE *fich)
{
  int d;
  fscanf(fich,"%d",&d);
  return d;
}

number ssiReadBigInt(ssiInfo *d)
{
   int sub_type=-1;
   fscanf(d->f_read,"%d",&sub_type);
   switch(sub_type)
   {
   case 3:
     {// read int or mpz_t or mpz_t, mpz_t
       number n=nlRInit(0);
       gmp_fscanf(d->f_read,"%Zd",n->z);
       n->s=sub_type;
       return n;
     }
   case 4: { int dd; fscanf(d->f_read,"%d",&dd); return INT_TO_SR(dd); }
   default: Werror("error in reading number: invalid subtype %d",sub_type);
            return NULL;
   }
}

number ssiReadNumber(ssiInfo *d)
{
  if (rField_is_Q(d->r))
  {
     int sub_type=-1;
     fscanf(d->f_read,"%d",&sub_type);
     switch(sub_type)
     {
     case 0:
     case 1:
       {// read int or mpz_t or mpz_t, mpz_t
        number n=nlRInit(0);
        mpz_init(n->n);
        gmp_fscanf(d->f_read,"%Zd %Zd",n->z,n->n);
        n->s=sub_type;
        return n;
       }

     case 3:
       {// read int or mpz_t or mpz_t, mpz_t
         number n=nlRInit(0);
         gmp_fscanf(d->f_read,"%Zd",n->z);
         n->s=sub_type;
         return n;
       }
     case 4: { int dd; fscanf(d->f_read,"%d",&dd); return INT_TO_SR(dd); }
     default: Werror("error in reading number: invalid subtype %d",sub_type);
              return NULL;
     }
  }
  else if (rField_is_Zp(d->r))
  {
    // read int
    int dd;
    fscanf(d->f_read,"%d",&dd);
    return (number)dd;
  }
  else Werror("coeffs not implemented");
  return NULL;
}

ring ssiReadRing(ssiInfo *d)
{
/* syntax is <ch> <N> <l1> <s1> ....<lN> <sN> */
  int ch, N,i,l;
  char **names;
  fscanf(d->f_read,"%d %d ",&ch,&N);
  names=(char**)omAlloc(N*sizeof(char*));
  for(i=0;i<N;i++)
  {
    names[i]=ssiReadString(d);
  }
  // read the orderings:
  int num_ord; // number of orderings
  fscanf(d->f_read,"%d",&num_ord);
  int *ord=(int *)omAlloc0((num_ord+1)*sizeof(int));
  int *block0=(int *)omAlloc0((num_ord+1)*sizeof(int));
  int *block1=(int *)omAlloc0((num_ord+1)*sizeof(int));
  for(i=0;i<num_ord;i++)
  {
     fscanf(d->f_read,"%d %d %d",&ord[i],&block0[i],&block1[i]);
  }
  return rDefault(ch,N,names,num_ord,ord,block0,block1);
}

poly ssiReadPoly(ssiInfo *D)
{
// < # of terms> < term1> < .....
  int n,i,l;
  n=ssiReadInt(D->f_read);
  //Print("poly: terms:%d\n",n);
  poly p;
  int j;
  j=0;
  poly ret=NULL;
  poly prev=NULL;
  for(l=0;l<n;l++) // read n terms
  {
// coef,comp.exp1,..exp N
    p=p_Init(D->r);
    pGetCoeff(p)=ssiReadNumber(D);
    int d;
    fscanf(D->f_read,"%d",&d);
    p_SetComp(p,d,D->r);
    for(i=1;i<=rVar(D->r);i++)
    {
      fscanf(D->f_read,"%d",&d);
      p_SetExp(p,i,d,D->r);
    }
    p_Setm(p,D->r);
    p_Test(p,D->r);
    if (ret==NULL) ret=p;
    else           pNext(prev)=p;
    prev=p;
 }
 return ret;
}

ideal ssiReadIdeal(ssiInfo *d)
{
  int n,i;
  ideal I;
  fscanf(d->f_read,"%d",&n);
  I=idInit(n,1);
  for(i=0;i<IDELEMS(I);i++) // read n terms
  {
    I->m [i]=ssiReadPoly(d);
  }
  return I;
}

matrix ssiReadMatrix(ssiInfo *d)
{
  int n,m,i,j;
  fscanf(d->f_read,"%d %d",&m,&n);
  matrix M=mpNew(m,n);
  poly p;
  for(int i=1;i<=MATROWS(M);i++)
    for(int j=1;j<=MATCOLS(M);j++)
    {
      p=ssiReadPoly(d);
      MATELEM(M,i,j)=p;
    }
  return M;
}

command ssiReadCommand(si_link l)
{
  ssiInfo *d=(ssiInfo*)l->data;
  // syntax: <num ops> <operation> <op1> <op2> ....
  command D=(command)omAlloc0(sizeof(*D));
  int argc,op;
  fscanf(d->f_read,"%d %d",&argc,&op);
  D->argc=argc; D->op=op;
  leftv v;
  if (argc >0)
  {
    v=ssiRead1(l);
    memcpy(&(D->arg1),v,sizeof(*v));
    omFreeBin(v,sleftv_bin);
  }
  if (argc <4)
  {
    if (D->argc >1)
    {
      v=ssiRead1(l);
      memcpy(&(D->arg2),v,sizeof(*v));
      omFreeBin(v,sleftv_bin);
    }
    if (D->argc >2)
    {
      v=ssiRead1(l);
      memcpy(&(D->arg3),v,sizeof(*v));
      omFreeBin(v,sleftv_bin);
    }
  }
  else
  {
    leftv prev=&(D->arg1);
    argc--;
    while(argc >0)
    {
      v=ssiRead1(l);
      prev->next=v;
      prev=v;
      argc--;
    }
  }
  return D;
}

procinfov ssiReadProc(ssiInfo *d)
{
  char *s=ssiReadString(d);
  procinfov p=(procinfov)omAlloc0Bin(procinfo_bin);
  p->language=LANG_SINGULAR;
  p->libname=omStrDup("");
  p->procname=omStrDup("");
  p->data.s.body=s;
  return p;
}
lists ssiReadList(si_link l)
{
  ssiInfo *d=(ssiInfo*)l->data;
  int nr;
  fscanf(d->f_read,"%d",&nr);
  lists L=(lists)omAlloc(sizeof(*L));
  L->Init(nr);

  int i;
  leftv v;
  for(i=0;i<nr;i++)
  {
    v=ssiRead1(l);
    memcpy(&(L->m[i]),v,sizeof(*v));
    omFreeBin(v,sleftv_bin);
  }
  return L;
}

//**************************************************************************/
BOOLEAN ssiOpen(si_link l, short flag)
{
  const char *mode;
  ssiInfo *d=(ssiInfo*)omAlloc0(sizeof(ssiInfo));
  if (flag & SI_LINK_OPEN)
  {
    if (l->mode[0] != '\0' && (strcmp(l->mode, "r") == 0))
      flag = SI_LINK_READ;
    else flag = SI_LINK_WRITE;
  }

  if (flag == SI_LINK_READ) mode = "r";
  else if (strcmp(l->mode, "w") == 0) mode = "w";
  else if (strcmp(l->mode, "fork") == 0) mode = "fork";
  else if (strcmp(l->mode, "tcp") == 0) mode = "tcp";
  else mode = "a";


  if (l->name[0] == '\0')
  {
    // ==============================================================
    if (strcmp(mode,"fork")==0)
    {
      int pc[2];
      int cp[2];
      pipe(pc);
      pipe(cp);
      pid_t pid=fork();
      if (pid==0) /*child*/
      {
        close(pc[1]); close(cp[0]);
        d->f_read=fdopen(pc[0],"r");
        d->fd_read=pc[0];
        d->f_write=fdopen(cp[1],"w");
        d->fd_write=cp[1];
        l->data=d;
        omFree(l->mode);
        l->mode = omStrDup(mode);
        SI_LINK_SET_OPEN_P(l, flag);
        myynest=0;
        fe_fgets_stdin=fe_fgets_dummy;
        loop
        {
          leftv h=ssiRead1(l); /*contains an exit.... */
          if (feErrors != NULL && *feErrors != '\0')
          {
            // handle errors:
            PrintS(feErrors); /* currently quite simple */
            *feErrors = '\0';
          }
          ssiWrite(l,h);
          h->CleanUp();
          omFreeBin(h, sleftv_bin);
        }
        /* never reached*/
      }
      else if (pid>0)
      {
        d->pid=pid;
        close(pc[0]); close(cp[1]);
        d->f_read=fdopen(cp[0],"r");
        d->fd_read=cp[0];
        d->f_write=fdopen(pc[1],"w");
        d->fd_write=pc[1];
        l->flags|=SI_LINK_READ|SI_LINK_WRITE;
      }
      else
      {
        Werror("fork failed (%d)",errno);
      }
    }
    // ==============================================================
    else if (strcmp(mode,"tcp")==0)
    {
      Print("name:>%s<\n",l->name);
      l->flags|=SI_LINK_READ|SI_LINK_WRITE;
    }
    // ==============================================================
    // stdin or stdout
    else if (flag == SI_LINK_READ)
    {
      d->f_read = stdin;
      mode = "r";
    }
    else
    {
      d->f_write = stdout;
      mode = "a";
    }
  }
  else
  {
    // normal ascii link to a file
    FILE *outfile;
    char *filename=l->name;

    if(filename[0]=='>')
    {
      if (filename[1]=='>')
      {
        filename+=2;
        mode = "a";
      }
      else
      {
        filename++;
        mode="w";
      }
    }
    outfile=myfopen(filename,mode);
    if (outfile!=NULL)
    {
      if (strcmp(l->mode,"r")==0) d->f_read = outfile;
      else d->f_write = outfile;
    }
    else
    {
      omFree(d);
      return TRUE;
    }
  }
  l->data=d;

  omFree(l->mode);
  l->mode = omStrDup(mode);
  SI_LINK_SET_OPEN_P(l, flag);
  return FALSE;
}

//**************************************************************************/
LINKAGE BOOLEAN ssiClose(si_link l)
{
  ssiInfo *d = (ssiInfo *)l->data;
  if (d!=NULL)
  {
    if (d->pid!=0) { fprintf(d->f_write,"99\n");fflush(d->f_write); }
    if (d->f_read!=NULL) fclose(d->f_read);
    if (d->f_write!=NULL) fclose(d->f_write);
    if (d->r!=NULL) rKill(d->r);
    if (d->pid!=0) { kill(d->pid,15); kill(d->pid,9); }
    omFreeSize((ADDRESS)d,(sizeof *d));
  }
  l->data=NULL;
  SI_LINK_SET_CLOSE_P(l);
  return FALSE;
}

//**************************************************************************/
LINKAGE leftv ssiRead1(si_link l)
{
  ssiInfo *d = (ssiInfo *)l->data;
  leftv res=(leftv)omAlloc0(sizeof(sleftv));
  int t=0;
  fscanf(d->f_read,"%d",&t);
  //Print("got type %d\n",t);
  switch(t)
  {
    case 1:res->rtyp=INT_CMD;
           res->data=(char *)ssiReadInt(d->f_read);
           break;
    case 2:res->rtyp=STRING_CMD;
           res->data=(char *)ssiReadString(d);
           break;
    case 3:res->rtyp=NUMBER_CMD;
           res->data=(char *)ssiReadNumber(d);
           break;
    case 4:res->rtyp=BIGINT_CMD;
           res->data=(char *)ssiReadBigInt(d);
           break;
    case 15:
    case 5:{
             d->r=ssiReadRing(d);
             d->r->ref++;
             res->rtyp=RING_CMD;
             res->data=(char*)d->r;
             // we are in the top-level, so set the basering to d->r:
             ssiSetCurrRing(d->r);
             if (t==15) return ssiRead1(l);
           }
           break;
    case 6:res->rtyp=POLY_CMD;
           if (d->r==NULL) goto no_ring;
           res->data=(char*)ssiReadPoly(d);
           break;
    case 7:res->rtyp=IDEAL_CMD;
           if (d->r==NULL) goto no_ring;
           res->data=(char*)ssiReadIdeal(d);
           break;
    case 8:res->rtyp=MATRIX_CMD;
           if (d->r==NULL) goto no_ring;
           res->data=(char*)ssiReadMatrix(d);
           break;
    case 9:res->rtyp=VECTOR_CMD;
           if (d->r==NULL) goto no_ring;
           res->data=(char*)ssiReadPoly(d);
           break;
    case 10:res->rtyp=MODUL_CMD;
           if (d->r==NULL) goto no_ring;
           res->data=(char*)ssiReadIdeal(d);
           break;
    case 11:
           {
             res->rtyp=COMMAND;
             res->data=ssiReadCommand(l);
             int nok=res->Eval();
             if (nok) WerrorS("error in eval");
             break;
           }
    case 12: /*DEF_CMD*/
           {
             res->rtyp=0;
             res->name=(char *)ssiReadString(d);
             int nok=res->Eval();
             if (nok) WerrorS("error in name lookup");
             break;
           }
    case 13: res->rtyp=PROC_CMD;
             res->data=ssiReadProc(d);
             break;
    case 14: res->rtyp=LIST_CMD;
             res->data=ssiReadList(l);
             break;
    case 99: ssiClose(l); exit(0);
    case 0: if (feof(d->f_read))
            {
              ssiClose(l);
              res->rtyp=DEF_CMD;
              break;
            }
    default: WerrorS("not implemented");
             omFreeSize(res,sizeof(sleftv));
             res=NULL;
             break;
  }
  return res;
no_ring: WerrorS("no ring");
  return NULL;
}
//**************************************************************************/
LINKAGE BOOLEAN ssiWrite(si_link l, leftv data)
{
  if(!SI_LINK_W_OPEN_P(l)) slOpen(l,SI_LINK_OPEN|SI_LINK_WRITE);
  ssiInfo *d = (ssiInfo *)l->data;
  d->level++;
  //FILE *fich=d->f;
  while (data!=NULL)
  {
    int tt=data->Typ();
    void *dd=data->Data();

    switch(tt /*data->Typ()*/)
    {
          case STRING_CMD: fprintf(d->f_write,"2 ");
                           ssiWriteString(d,(char *)dd);
                           break;
          case INT_CMD: fprintf(d->f_write,"1 ");
                        ssiWriteInt(d,(int)(long)dd);
                        break;
          case BIGINT_CMD:fprintf(d->f_write,"4 ");
                        ssiWriteBigInt(d,(number)dd);
                        break;
          case NUMBER_CMD:
                          if (d->r!=currRing)
                          {
                            fprintf(d->f_write,"15 ");
                            ssiWriteRing(d,currRing);
                            if (d->level<=1) fprintf(d->f_write,"\n");
                          }
                          fprintf(d->f_write,"3 ");
                          ssiWriteNumber(d,(number)dd);
                        break;
          case RING_CMD:fprintf(d->f_write,"5 ");
                        ssiWriteRing(d,(ring)dd);
                        break;
          case POLY_CMD:
          case VECTOR_CMD:
                        if (d->r!=currRing)
                        {
                          fprintf(d->f_write,"15 ");
                          ssiWriteRing(d,currRing);
                          if (d->level<=1) fprintf(d->f_write,"\n");
                        }
                        if(tt==POLY_CMD) fprintf(d->f_write,"6 ");
                        else             fprintf(d->f_write,"9 ");
                        ssiWritePoly(d,tt,(poly)dd);
                        break;
          case IDEAL_CMD:
          case MODUL_CMD:
          case MATRIX_CMD:
                        if (d->r!=currRing)
                        {
                          fprintf(d->f_write,"15 ");
                          ssiWriteRing(d,currRing);
                          if (d->level<=1) fprintf(d->f_write,"\n");
                        }
                        if(tt==IDEAL_CMD)       fprintf(d->f_write,"7 ");
                        else if(tt==MATRIX_CMD) fprintf(d->f_write,"8 ");
                        else                    fprintf(d->f_write,"10 ");
                        ssiWriteIdeal(d,tt,(ideal)dd);
                        break;
          case COMMAND:
                   fprintf(d->f_write,"11 ");
                   ssiWriteCommand(l,(command)dd);
                   break;
          case DEF_CMD: /* not evaluated stuff in quotes */
                   fprintf(d->f_write,"12 ");
                   ssiWriteString(d,data->Name());
                   break;
          case PROC_CMD:
                   fprintf(d->f_write,"13 ");
                   ssiWriteProc(d,(procinfov)dd);
                   break;
          case LIST_CMD:
                   fprintf(d->f_write,"14 ");
                   ssiWriteList(l,(lists)dd);
                   break;
          default: Werror("not implemented (t:%d, rtyp:%d)",tt, data->rtyp);
                   d->level=0;
                   return TRUE;
    }
    if (d->level<=1) { fprintf(d->f_write,"\n"); fflush(d->f_write); }
    data=data->next;
  }
  d->level--;
  return FALSE;
}

si_link_extension slInitSsiExtension(si_link_extension s)
{
  s->Open=(slOpenProc)ssiOpen;
  s->Close=(slCloseProc)ssiClose;
  s->Kill=(slKillProc)ssiClose;
  s->Read=(slReadProc)ssiRead1;
  s->Read2=(slRead2Proc)NULL;
  s->Write=(slWriteProc)ssiWrite;

  s->Status=slStatusSsi;
  s->type="ssi";
  return s;
}
const char* slStatusSsi(si_link l, const char* request)
{
  ssiInfo *d=(ssiInfo*)l->data;
  if (d==NULL) return "not open";
  if ((strcmp(l->mode,"fork")==0) && (strcmp(request, "read") == 0))
  {
    fd_set  mask, fdmask;
    struct timeval wt;
    loop
    {
      /* Don't block. Return socket status immediately. */
      wt.tv_sec  = 0;
      wt.tv_usec = 0;

      FD_ZERO(&mask);
      FD_SET(d->fd_read, &mask);
      //Print("test fd %d\n",d->fd_read);
    /* check with select: chars waiting: no -> not ready */
      switch (select(d->fd_read+1, &mask, NULL, NULL, &wt))
      {
        case 0: /* not ready */ return "not ready";
        case -1: /*error*/      return "error";
        case 1: /*ready ? */    break;
      }
    /* yes: read 1 char*/
    /* if \n, check again with select else ungetc(c), ready*/
      int c=fgetc(d->f_read);
      //Print("try c=%d\n",c);
      if (c== -1) return "eof";
      else if (isdigit(c))
      { ungetc(c,d->f_read); return "ready"; }
      else if ((c!=' ') && (c!='\n'))
      {
        Werror("unknown char in ssiLink(%d)",c);
        return "error";
      }
      /* else: next char */
    }
  }
  else if (strcmp(request, "read") == 0)
  {
    if (SI_LINK_R_OPEN_P(l) && (!feof(d->f_read))) return "ready";
    else return "not ready";
  }
  else if (strcmp(request, "write") == 0)
  {
    if (SI_LINK_W_OPEN_P(l)) return "ready";
    else return "not ready";
  }
  else return "unknown status request";
}

// ----------------------------------------------------------------
// format
// 1 int %d
// 2 string <len> %s
// 3 number
// 4 bigint 4 %d or 3 <mpz_t>
// 5 ring
// 6 poly
// 7 ideal
// 8 matrix
// 9 vector
// 10 module
// 11 command
// 12 def <len> %s
// 13 proc <len> %s
// 14 list %d <elem1> ....
// 15 setring .......
//
