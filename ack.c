#include <stdio.h>
#include <time.h>

int ack(int i, int j) {
    if (i == 0) {
        return j + 1;
    } else if (j == 0) {
        return ack(i - 1, 1);
    } else {
        return ack(i - 1, ack(i, j - 1));
    }
}

int main() {
    clock_t start_time = clock();
    int result = ack(3, 11);
    clock_t end_time = clock();
    double time_taken = (double)(end_time - start_time) / CLOCKS_PER_SEC;
    printf("Ack(%d, %d) = %d\n", i, j, result);
    printf("Time taken: %f seconds\n", time_taken);
    return 0;
}