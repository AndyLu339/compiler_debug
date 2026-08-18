int main() {
    int i = 0;
    int sum = 0;
    while (i < 10) {
        sum = sum + i;
        i = i + 1;
        if (i == 5) {
            int temp = i;
            i = temp;
        }
    }
    return sum;
}


