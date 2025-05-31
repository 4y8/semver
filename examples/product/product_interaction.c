void main() {
	int i = rand(-3, 1);

	if (i % 3 == 0 && i < 0) {
		if (i < 0) {
			assert(i == -3); // @OK
		}
	}
}

