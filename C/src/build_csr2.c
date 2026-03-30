/* THIS ALTERNATE IMPLEMENTATION OF BUILD_CSR
     (which is not debugged or proved yet!)
   has two properties that the original does not:
    (1) bit-for-bit reproducibility is improved, because it guarantees to add 
        the duplicates in the original order they appear in the COO entries;
    (2) "Reassembly", that is, updating the values in a CSR matrix from new values in the COO
    matrix, provided that the row and column indexes in the COO have not changed, is now
    possible (and efficient).
*/

#include <sparse.h>

void exit(int code);
void free(void *p);

/* not really used in this file */
// struct coo_matrix *create_coo_matrix (unsigned maxn, unsigned rows, unsigned cols) {
//   struct coo_matrix *p = surely_malloc (sizeof (*p));
//   p->row_ind = (unsigned *)surely_malloc(maxn * sizeof(unsigned));
//   p->col_ind = (unsigned *)surely_malloc(maxn * sizeof(unsigned));
//   p->val = (double *)surely_malloc(maxn * sizeof(double));
//   p->n=0;
//   p->maxn=maxn;
//   p->rows=rows; p->cols=cols;
//   return p;
// }

// void add_to_coo_matrix(struct coo_matrix *p, unsigned i, unsigned j, double x) {
//   unsigned n = p->n;
//   if (n>=p->maxn) exit(2);
//   p->row_ind[n]=i;
//   p->col_ind[n]=j;
//   p->val[n]=x;
//   p->n = n+1;
// }

/* end of not used code */

struct rowcol {unsigned row,col;};

void swap_rc(struct rowcol *p, unsigned a, unsigned b) {
  unsigned i,j;
  i=p[a].row;
  j=p[a].col;
  p[a].row=p[b].row;
  p[a].col=p[b].col;
  p[b].row=i;
  p[b].col=j;
}

int coog_less (struct rowcol *p, unsigned a, unsigned b) {
  unsigned ra = p[a].row, rb = p[b].row;
  if (ra<rb) return 1;
  if (ra>rb) return 0;
  return p[a].col < p[b].col;
}

/* adapted from qsort3 in cbench:
   https://github.com/cverified/cbench/blob/master/src/qsort/qsort3.c */

/* sort the coordinate elements of a coo_matrix */
/* different input types; adjust the funspec */
void coog_quicksort(struct rowcol *p, unsigned base, unsigned n)
{
  unsigned lo, hi, left, right, mid;

  if (n == 0)
    return;
  lo = base;
  hi = lo + n - 1;
  while (lo < hi) {
    mid = lo + ((hi - lo) >> 1);
    
    if (coog_less(p, mid,lo))
      swap_rc(p, mid, lo);
    if (coog_less(p, hi,mid)) {
      swap_rc(p, mid, hi);
      if (coog_less(p,mid,lo))
        swap_rc(p, mid, lo);
    }
    left = lo + 1;
    right = hi - 1;
    do {
      while (coog_less(p,left,mid))
        left++;
      while (coog_less(p,mid,right))
        right--;
      if (left < right) {
	swap_rc(p, left, right);
        if (mid == left)
          mid = right;
        else if (mid == right)
          mid = left;
        left++;
        right--;
      } else if (left == right) {
        left++;
        right--;
        break;
      }
    } while (left <= right);
    if (right - lo > hi - left) {
      coog_quicksort(p, left, hi - left + 1);
      hi = right;
    } else {
      coog_quicksort(p, lo, right - lo + 1);
      lo = left;
    }
  }
}

/* Count the number of distinct row/col entries in a sorted coordinate list */
/* Only called when the rowcol is sorted */
unsigned coog_count (unsigned n, struct rowcol *p) {
  unsigned i,r,c,ri,ci,count;
  count=0;
  r=-1;
  c=0;
  for (i=0; i<n; i++) {
    ri=p[i].row; 
    ci=p[i].col;
    if (ri!=r || ci!=c) {
      count++;
      r=ri; c=ci;
    }
  }
  return count;
}

struct rowcol *start_coog(unsigned n) {
  return (struct rowcol *) surely_malloc(n * sizeof(struct rowcol));
}

/* Think about whether to change the data structure list rowcol */
/* Only add to the end of the list */
void add_to_coog(struct rowcol *rc, unsigned i, unsigned r, unsigned c) {
  rc[i].row = r;
  rc[i].col = c;
}

void coog_to_csrg_aux(struct rowcol *rc, unsigned n, unsigned rows, unsigned *col_ind, unsigned *row_ptr)
{
  unsigned r, c, ri, ci, l, i;
  r = -1; 
  c = 0;
  l = 0;
  for (i = 0; i < n; i++){
    ri = rc[i].row;
    ci = rc[i].col;
    if (ri == r) 
      if (ci == c);
      else {
        c = ci;
        col_ind[l] = ci;
        l++;
      }
    else {
      while (r+1 <= ri) row_ptr[++r] = l;
      c = ci;
      col_ind[l] = ci;
      l++;
    }
  }
  while (r+1 <= rows) row_ptr[++r] = l;
}

struct csr_matrix *coog_to_csrg(struct rowcol *rc, unsigned n, unsigned rows, unsigned cols)
{
  struct csr_matrix *q;
  unsigned k;
  unsigned *col_ind, *row_ptr;
  coog_quicksort(rc, 0, n);
  k = coog_count(n, rc);
  col_ind = surely_malloc(k * sizeof(unsigned));
  row_ptr = surely_malloc((rows+1) * sizeof(unsigned));

  coog_to_csrg_aux(rc, n, rows, col_ind, row_ptr);
  // free(rc);

  q = surely_malloc(sizeof(struct csr_matrix));
  q->val = surely_malloc(k * sizeof(double));
  q->col_ind = col_ind;
  q->row_ptr = row_ptr;
  q->rows = rows;
  q->cols = cols;
  return q;
}

/* the following function is divided into two */
// struct csr_matrix *coog_to_csrg_old(struct rowcol *rc, unsigned n, unsigned rows, unsigned cols) {
//   struct csr_matrix *q;
//   unsigned i;
//   unsigned r,c, ri, ci, k, l;
//   unsigned *col_ind, *row_ptr;
//   coog_quicksort(rc, 0, n);
//   k = coog_count(n,rc);
//   q = surely_malloc(sizeof(struct csr_matrix));
//   col_ind = surely_malloc(k * sizeof(unsigned));
//   row_ptr = surely_malloc ((rows+1) * sizeof(unsigned));
//   r=-1;
//   c=0; /* this line is unnecessary for correctness but simplifies the proof */
//   l=0;
//   /* partial_csr_0 */
//   for (i=0; i<n; i++) {
//     ri = rc[i].row;
//     ci = rc[i].col;
//     if (ri==r)
//       if (ci==c)
// 	/*skip*/; /* partial_CSR_duplicate */
//       else {
// 	c=ci;
// 	col_ind[l] = ci;
// 	l++;           /* partial_CSR_newcol */
//       }
//     else {
//       while (r+1<=ri) row_ptr[++r]=l; /* partial_CSR_skiprow */
//       c= ci;
//       col_ind[l] = ci;
//       l++;            /* partial_CSR_newrow */
//     }
//   }
//   while (r+1<=rows) row_ptr[++r]=l;  /* partial_CSR_lastrows */
//   free(rc);
//   q->val = surely_malloc(k * sizeof(double));
//   q->col_ind = col_ind;
//   q->row_ptr = row_ptr;
//   q->rows = rows;
//   q->cols = cols;
//   return q;          /* partial_CSR_properties */
// }


void reset_csr(struct csr_matrix *q) {
  unsigned rows,i,n;
  double *val;
  rows = q->rows;
  n = q->row_ptr[rows];
  val = q->val;
  for (i=0; i<n; i++) val[i]=0.0;
}

void add_to_csr(struct csr_matrix *q, unsigned r, unsigned c, double x) {
  unsigned lo, mid, hi, *row_ptr, *col_ind;
  double *val;
  row_ptr = q->row_ptr;
  col_ind = q->col_ind;
  val = q->val;
  lo = row_ptr[r];
  hi = row_ptr[r+1];
  while (lo+1<hi) {
      /* invariant: row_ptr[r] <= lo < hi <= row_ptr[r+1]
	          /\ col_ind[lo]<=c /\ c < col_ind[hi]
                  /\ exists i, lo<=i<hi /\ c=col_ind[i] */
      mid=lo + ((hi-lo)>>1);
      if (c<col_ind[mid])
	hi=mid;
      else lo=mid;
    }
    /* loop postcondition: row_ptr[r] <= lo < row_ptr[r+1] /\ c = col_ind[lo] */
    val[lo]+=x;
}

// struct csr_matrix *coo_to_csr_matrix(struct coo_matrix *p) {
//   unsigned *prow_ind, *pcol_ind, i, n;
//   double *pval;
//   struct csr_matrix *q;
//   n=p->n;
//   prow_ind=p->row_ind;
//   pcol_ind=p->col_ind;
//   pval = p->val;    
//   struct rowcol *rc = start_coo_shell(n);
//   for (i=0; i<n; i++) 
//     add_to_coo_shell(rc,i,prow_ind[i],pcol_ind[i]);
//   free(rc);
//   q = coo_shell_to_csr_shell(rc,n,p->rows,p->cols);
//   reset_csr_shell(q);
//   for (i=0; i<n; i++)
//     add_to_csr_shell(q,prow_ind[i],pcol_ind[i],pval[i]);
//   return q;
// }

