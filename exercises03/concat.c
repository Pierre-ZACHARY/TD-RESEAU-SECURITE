#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>


/*@ requires INT_MIN < size1 + size2 < INT_MAX;
    requires \valid(t1 + (0..size1-1));
    requires \valid(t2 + (0..size2-1));
    requires \valid(dst + (0..size1+size2-1));
    requires \separated(t1 + (0..size1-1),t2 + (0..size2-1));
    requires \separated(t1 + (0..size1-1),dst + (0..size1+size2-1));
    requires \separated(t2 + (0..size2-1),dst + (0..size1+size2-1));
    assigns *(dst + (0..size1+size2-1));
    ensures \forall integer i; 0<=i<size1 ==> dst[i] == t1[i];
    ensures \forall integer i; size1<=i<size1+size2 ==> dst[i] == t2[i-size1];
     */
void concat(int * t1, size_t size1, int * t2, size_t size2, int * dst)
{
    /*@
      loop invariant 0 <= i <= size1 + size2;
      loop invariant \forall integer k; 0 <= k < size1 && k<i ==> dst[k] == t1[k];
      loop invariant \forall integer k; size1 <= k < size1+size2 && k<i ==> dst[k] == t2[k-size1];
      loop assigns i;
      loop assigns *(dst + (0..size1+size2-1));
      loop variant size1 + size2 - i;
      */
  for(size_t i = 0; i < size1 + size2; i++){
      if (i < size1)
          dst[i] = t1[i];
      else
          dst[i] = t2[i - size1];
  }

}


int main(){
    printf("%llu", sizeof(unsigned long long));
    return 0;
}

