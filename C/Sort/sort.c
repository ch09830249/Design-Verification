// Bubble Sort（氣泡排序）
void bubble_sort(int arr[], int n) {
    for (int i = 0; i < n-1; i++)
        for (int j = 0; j < n-i-1; j++)
            if (arr[j] > arr[j+1]) {
                int tmp = arr[j];
                arr[j] = arr[j+1];
                arr[j+1] = tmp;
            }
}

// Selection Sort（選擇排序）
void selection_sort(int arr[], int n) {
    for (int i = 0; i < n-1; i++) {
        int min_idx = i;
        for (int j = i+1; j < n; j++)
            if (arr[j] < arr[min_idx])
                min_idx = j;
        int tmp = arr[i];
        arr[i] = arr[min_idx];
        arr[min_idx] = tmp;
    }
}

// Insertion Sort（插入排序）
void insertion_sort(int arr[], int n) {
    for (int i = 1; i < n; i++) {
        int key = arr[i];
        int j = i - 1;
        while (j >= 0 && arr[j] > key) {
            arr[j+1] = arr[j];
            j--;
        }
        arr[j+1] = key;
    }
}

// Merge Sort（合併排序）
void merge(int arr[], int l, int m, int r) {
    int n1 = m - l + 1, n2 = r - m;
    int L[n1], R[n2];
    for (int i = 0; i < n1; i++) L[i] = arr[l + i];
    for (int j = 0; j < n2; j++) R[j] = arr[m + 1 + j];

    int i = 0, j = 0, k = l;
    while (i < n1 && j < n2)
        arr[k++] = (L[i] <= R[j]) ? L[i++] : R[j++];
    while (i < n1) arr[k++] = L[i++];
    while (j < n2) arr[k++] = R[j++];
}

void merge_sort(int arr[], int l, int r) {
    if (l < r) {
        int m = l + (r - l)/2;
        merge_sort(arr, l, m);
        merge_sort(arr, m+1, r);
        merge(arr, l, m, r);
    }
}

// Quick Sort（快速排序）
int partition(int arr[], int low, int high) {
    int pivot = arr[high];
    int i = low - 1;
    for (int j = low; j < high; j++)
        if (arr[j] < pivot) {
            i++;
            int tmp = arr[i];
            arr[i] = arr[j];
            arr[j] = tmp;
        }
    int tmp = arr[i+1];
    arr[i+1] = arr[high];
    arr[high] = tmp;
    return i + 1;
}

void quick_sort(int arr[], int low, int high) {
    if (low < high) {
        int pi = partition(arr, low, high);
        quick_sort(arr, low, pi - 1);
        quick_sort(arr, pi + 1, high);
    }
}

// Heap Sort（堆積排序）
void heapify(int arr[], int n, int i) {
    int largest = i; 
    int l = 2*i + 1; 
    int r = 2*i + 2; 

    if (l < n && arr[l] > arr[largest])
        largest = l;
    if (r < n && arr[r] > arr[largest])
        largest = r;
    if (largest != i) {
        int tmp = arr[i];
        arr[i] = arr[largest];
        arr[largest] = tmp;
        heapify(arr, n, largest);
    }
}

void heap_sort(int arr[], int n) {
    for (int i = n/2 - 1; i >= 0; i--)
        heapify(arr, n, i);
    for (int i = n-1; i >= 0; i--) {
        int tmp = arr[0];
        arr[0] = arr[i];
        arr[i] = tmp;
        heapify(arr, i, 0);
    }
}

/*
方法					平均時間			穩定			適用場景
Bubble / Selection		O(n²)				❌			學習用、小資料量
Insertion				O(n²)				✅			幾乎有序的資料
Merge Sort			 O(n log n)				✅		大筆資料、需要穩定排序
Quick Sort			 O(n log n)				❌		實際效能高（最常用）
Heap Sort			 O(n log n)				❌		節省記憶體、不需穩定性
*/

// Counting Sort（計數排序）
void counting_sort(int arr[], int n, int max_val) {
    int count[max_val + 1];
    int output[n];

    // 初始化
    for (int i = 0; i <= max_val; i++) count[i] = 0;
    for (int i = 0; i < n; i++) count[arr[i]]++;

    // 累積
    for (int i = 1; i <= max_val; i++) count[i] += count[i - 1];

    // 放入 output（從後面放才能穩定）
    for (int i = n - 1; i >= 0; i--)
        output[--count[arr[i]]] = arr[i];

    // 回填原陣列
    for (int i = 0; i < n; i++) arr[i] = output[i];
}

// Radix Sort（基數排序）
int get_max(int arr[], int n) {
    int max = arr[0];
    for (int i = 1; i < n; i++)
        if (arr[i] > max)
            max = arr[i];
    return max;
}

void count_sort_radix(int arr[], int n, int exp) {
    int output[n], count[10] = {0};

    for (int i = 0; i < n; i++)
        count[(arr[i] / exp) % 10]++;

    for (int i = 1; i < 10; i++)
        count[i] += count[i - 1];

    for (int i = n - 1; i >= 0; i--)
        output[--count[(arr[i] / exp) % 10]] = arr[i];

    for (int i = 0; i < n; i++)
        arr[i] = output[i];
}

void radix_sort(int arr[], int n) {
    int max = get_max(arr, n);
    for (int exp = 1; max / exp > 0; exp *= 10)
        count_sort_radix(arr, n, exp);
}

// Bucket Sort（桶子排序）
#include <stdio.h>
#include <stdlib.h>

void insertion_sort(float* arr, int n) {
    for (int i = 1; i < n; i++) {
        float key = arr[i];
        int j = i - 1;
        while (j >= 0 && arr[j] > key)
            arr[j + 1] = arr[j--];
        arr[j + 1] = key;
    }
}

void bucket_sort(float arr[], int n) {
    float* buckets[n];
    int count[n];
    for (int i = 0; i < n; i++) {
        buckets[i] = (float*)malloc(n * sizeof(float));
        count[i] = 0;
    }

    for (int i = 0; i < n; i++) {
        int idx = n * arr[i];
        buckets[idx][count[idx]++] = arr[i];
    }

    for (int i = 0; i < n; i++)
        insertion_sort(buckets[i], count[i]);

    int k = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < count[i]; j++)
            arr[k++] = buckets[i][j];

    for (int i = 0; i < n; i++) free(buckets[i]);
}

// Shell Sort（希爾排序）
void shell_sort(int arr[], int n) {
    for (int gap = n/2; gap > 0; gap /= 2) {
        for (int i = gap; i < n; i++) {
            int temp = arr[i], j;
            for (j = i; j >= gap && arr[j - gap] > temp; j -= gap)
                arr[j] = arr[j - gap];
            arr[j] = temp;
        }
    }
}

// Gnome Sort（花園精靈排序）
void gnome_sort(int arr[], int n) {
    int i = 0;
    while (i < n) {
        if (i == 0 || arr[i] >= arr[i - 1])
            i++;
        else {
            int tmp = arr[i];
            arr[i] = arr[i - 1];
            arr[i - 1] = tmp;
            i--;
        }
    }
}

// Cocktail Sort（雙向氣泡）
void cocktail_sort(int arr[], int n) {
    int swapped = 1;
    int start = 0, end = n - 1;

    while (swapped) {
        swapped = 0;
        for (int i = start; i < end; i++) {
            if (arr[i] > arr[i + 1]) {
                int tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                swapped = 1;
            }
        }
        if (!swapped) break;
        swapped = 0;
        end--;
        for (int i = end - 1; i >= start; i--) {
            if (arr[i] > arr[i + 1]) {
                int tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                swapped = 1;
            }
        }
        start++;
    }
}
