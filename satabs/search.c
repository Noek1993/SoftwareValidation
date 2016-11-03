#define N 64

int nondet_int();

int array[N];

int search(int v, int n) {
   __CPROVER_assume(n >= 0 && n <= N);
   int first = 0;
   int last = n - 1;
   int middle = (first+last)/2;
   assert (first == 0 && last == n-1);
   while (first <= last) {
      __CPROVER_assume(first >=0);
      __CPROVER_assume(last < N);
      if (array[middle] < v) {
         first = middle+1;
		} else if (array[middle] == v) {
         return 1;
      } else {
         last = middle-1;
      }
      middle = (first+last)/2;
      assert(middle >= 0 && middle < N);
   }
   return 0; 
}

int main(void) {
   search(nondet_int(), N);
   return 0;
}