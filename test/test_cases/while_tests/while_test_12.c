
int main() {
    int neg_i = -5;
    int sum = 0;
    while (neg_i < 0) {
        sum = sum + neg_i;
        neg_i = neg_i + 1;
    }
    return sum;
}


