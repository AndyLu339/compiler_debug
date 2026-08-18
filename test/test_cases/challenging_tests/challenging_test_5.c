int main() {
    int outer_i = 0;
    int inner_j = 0;
    int counter = 0;
    while (outer_i < 3) {
        inner_j = 0;
        while (inner_j < 3) {
            if (outer_i == 1 && inner_j == 1) {
                inner_j = inner_j + 1;
                continue;
            }
            if (outer_i == 2 && inner_j == 2) {
                break;
            }
            counter = counter + 1;
            inner_j = inner_j + 1;
        }
        outer_i = outer_i + 1;
    }
    return counter;
}


