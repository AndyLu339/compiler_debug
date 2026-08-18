
int main() {
    int i = 0;
    int j = 0;
    int count = 0;
    while (i < 3) {
        j = 0;
        while (j < 2) {
            count = count + 1;
            j = j + 1;
        }
        i = i + 1;
    }
    return count;
}


