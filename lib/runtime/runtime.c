#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>

/* [read_all(fd, buf, n)] reads exactly [n] bytes of data from the file
 * descriptor [fd] into [buf], then adds a null byte at the end. Prints an
 * error and exits if there is a problem with a read (for instance, if the file
 * descriptor isn't open for reading).
 */
int read_all(int fd, char *buf, int n) {
  int total_read = 0;
  while (total_read < n) {
    int read_this_time = read(fd, buf + total_read, n - total_read);
    if (read_this_time < 0) {
      printf("Read error\n");
      exit(1);
    } else if (read_this_time == 0) {
      // printf("num to read: %d\n", n);
      // printf("read so far: %d\n", total_read);
      printf("Unexpected EOF\n");
      exit(1);
    }
    total_read += read_this_time;
  }
  buf[n] = '\0';
  total_read++;
  if (total_read % 8 == 0) {
    return total_read;
  } else {
    return total_read + 8 - (total_read % 8);
  }
}

/* [write_all(fd, buf)] writes the null_terminated string [buf] to the file
 * descriptor [fd]. Prints an error and exits if there is a problem with a
 * write (for instance, if the file descriptor isn't open for writing).
 */
void write_all(int fd, char *buf) {
  // printf("%d\n", fd);
  int total = strlen(buf);
  int total_written = 0;
  while (total_written < total) {
    int written_this_time = write(fd, buf + total_written, total - total_written);
    if (written_this_time < 0) {
      printf("Write error\n");
      exit(1);
    }
    total_written += written_this_time;
  }
}

/* [open_for_reading(filename)] opens the file named [filename] in read-only
 * mode and returns a file descriptor, printing an error and exiting if there
 * is a problem (e.g., if the file does not exist).
 */
int open_for_reading(char *filename) {
  int fd = open(filename, O_RDONLY);
  if (fd < 0) {
    printf("Open error\n");
    exit(1);
  }
  return fd;
}

/* [open_for_writing(filename)] opens the file named [filename] in write-only
 * mode (creating it if it doesn't exist) and returns a file descriptor,
 * printing an error and exiting if there is a problem (e.g., if the file is in
 * a directory that doesn't exist).
 */
int open_for_writing(char *filename) {
  int fd = open(filename, O_WRONLY | O_CREAT, 0644);
  if (fd < 0) {
    printf("Open error\n");
    exit(1);
  }
  // printf("%d\n", fd);
  return fd;
}

int close_channel(int fd) {
  int success = close(fd);
  if (success < 0) {
    printf("Close error\n");
    exit(1);
  }
  return 1;
}


extern uint64_t lisp_entry(void *heap);

#define num_mask   0b11
#define num_tag    0b00
#define num_shift  2

#define bool_mask  0b1111111
#define bool_tag   0b0011111
#define bool_shift 7

#define heap_mask 0b111
#define pair_tag 0b010

#define string_tag 0b011
#define channel_shift 9
#define channel_mask 0b111111111
#define in_channel_tag 0b011111111
#define out_channel_tag 0b001111111

void print_value(uint64_t value) {
  if ((value & num_mask) == num_tag) {
    int64_t ivalue = (int64_t)value;
    printf("%" PRIi64, ivalue >> num_shift);
  } else if ((value & bool_mask) == bool_tag) {
    if (value >> bool_shift) {
      printf("true");
    }
    else {
      printf("false");
    }
  } else if ((value & heap_mask) == pair_tag) {
    uint64_t v1 = *(uint64_t *)(value - pair_tag);
    uint64_t v2 = *(uint64_t *)(value - pair_tag + 8);
    printf("(pair ");
    print_value(v1);
    printf(" ");
    print_value(v2);
    printf(")");
  } else if ((value & heap_mask) == string_tag){
    char* addr = (char*) ((value >> 3) << 3);
    printf("\"");
    int i = 0;
    while (addr[i]  != '\0') {
      if (addr[i] == '\n') {
        printf("\\n");
      } else if (addr[i] == '\"'){
        printf("\\\"");
      } else {
        printf("%c", addr[i]);
      }
      // addr += 8;
      i++;
    }
    printf("\"");
  } else if ((value & channel_mask) == in_channel_tag) {
    printf("<in-channel>");
  } else if ((value & channel_mask) == out_channel_tag) {
    printf("<out-channel>");
  } else {
    printf("BAD VALUE: %" PRIu64, value);
  }
}

void lisp_error(char *exp) {
  printf("Stuck[%s]", exp);
  exit(1);
}

int main(int argc, char **argv) {
  void *heap = malloc(4096);
  lisp_entry(heap);
  return 0;
}

uint64_t read_num() {
  int r;
  scanf("%d", &r);
  return (uint64_t)(r) << num_shift;
}

void print_newline() {
  printf("\n");
}
