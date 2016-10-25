#define N 64

int nondet_int();

int array[N];

int search(int v, int n) {
   int first = 0;
   int last = n - 1;
   int middle = (first+last)/2;
   while (first <= last) {
      if (array[middle] < v) {
         first = middle+1;
			} else if (array[middle] == v) {
         return 1;
      } else {
         last = middle-1;
      }
      middle = (first+last)/2;
   }
   return 0; 
}

int main(void) {
   search(nondet_int(), N);
   return 0;
}