
int main() {
    int i = 0;
    int sum = 0;
    int product = 1;
    while (i < 4) {
        sum = sum + i;
        product = product * (i + 1);
        i = i + 1;
    }
    return sum + product;
}


