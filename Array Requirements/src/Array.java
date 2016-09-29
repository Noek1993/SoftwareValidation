
public class Array {

	/*@ spec_public */ private int[] B;	// The array
	/*@ spec_public */ private int n;	// Lenght of the array
	/*@ spec_public */ private int j;	// Index start
	/*@ spec_public */ private int k;	// Index end
	
	//@ public invariant j >= 0 && j < k && k < n;
	
	// 1A
	//@ public invariant (\forall int i1; i1 >= j && i1 <= k; (\exists int i2; (i2 >= 0 && i2 < j) || (i2 > k && i2 < n); B[i1] == B[i2]));
	
	// 1b
	//@ public invariant (\forall int i1, i2; i1 >= 0 && i2 > i1 && i2 < n; (B[i1] == B[i2]) ==> ((i1 >= j && i1 <= k) || (i2 >= j && i2 <= k)));

	// 1c
	//@ public invariant (\forall int i1,i2,i3; i1 >= 0 && i2 > i1 && i3 > i2 && i3 < n; B[i1] != B[i2] || B[i2] != B[i3] || B[i1] != B[i3]);
	
	// 1d
	//@ public invariant (\exists int i1, i2; i1 >= 0 && i2 > i1 && i2 < n; B[i1] == B[i2] && (\forall int i3; i3 >= 0 && i3 < n; B[i1] >= B[i3]));
	
	// 1e
	// index i1 and i2 are  segrement with lenght k, after this we check for the palindrome, we consider the segment i1,i2 a sub array
	//@ public invariant (\exists int i1, i2; i1 >= 0 && i2 == (i1 + k -1) && i2 < n; (\forall int i3; i3 >= 0 && i3 < k; B[i1 + i3] == B[i2 - i3]));
	
	// 1flsls
	
	/*@ public invariant (\exists int i1, i2; i1 >= 0 && i2 > i1 && i2 < n; (\forall int i3; i3 >= 1 && i3 < n; 
		B[i3-1] <= B[i3] || (i3 == i1 && B[i3-1] <= B[i2]) || (i3-1 == i2 && B[i1] <= B[i3]) || (i3-1 == i1 && i3 == i2 && B[i2] <= B[i1]) ) );
	 @*/
	
	// 1g
	/*@ public invariant (\exists int i1; i1 >= 0 && i1 < n; (\forall int i2; i2 >= 0 && i2 < n && B[i1] != B[i2]; 
	  	(\sum int s1; s1 >= 0 && s1 <= n && B[s1] == B[i1]; 1) > (\sum int s2; s2 >= 0 && s2 <= n && B[s2] == B[i2]; 1) ) );
	 @*/
}








