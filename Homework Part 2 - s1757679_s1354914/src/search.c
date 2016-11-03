// Koen Mulder (s1757679) and Ruben van den Berg (s1354914)

#define N 64

int nondet_int();

int array[N];

int search(int v, int n) {
   assert(n == N);
   int first = 0;
   int last = n - 1;
   int middle = (first+last)/2;
   while (first <= last) {
      __CPROVER_assume(first >=0);
      __CPROVER_assume(last < N);
      if (array[middle] < v) {
         first = middle+2;
		} else if (array[middle] == v) {
         return 1;
      } else {
         last = middle-2;
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