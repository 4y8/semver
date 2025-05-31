void main(){
	int i = rand(1, 10);
	int j = 6 * i;
	int k = j / 3;
	assert(k % 2 == 0); //@OK
	assert(k % 3 == 0); //@KO
}
