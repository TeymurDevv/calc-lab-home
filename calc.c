// Teymur Suleymanov 251ADB097
// (optional) https://github.com/TeymurDevv/calc-lab-home
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used:
// - My own C language skills.
// - Lab 1-5 examples from my repo.
// https://github.com/TeymurDevv/Programming_Languages_C_2026_Fall_Labs/
// https://craftinginterpreters.com/scanning.html
// https://craftinginterpreters.com/parsing-expressions.html
// https://cp-algorithms.com/algebra/binary-exp.html
// https://craftinginterpreters.com/chunks-of-bytecode.html
// https://chatgpt.com/s/cx_6ade60be2f208191bb26b5edb206e1e8

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#define FIRST_NAME "teymur"
#define LAST_NAME "suleymanov"
#define STUDENT_ID "251adb097"

typedef struct Value {
  long long integer_value;
  double float_value;
  int is_float;
} Value;

typedef enum TokenType {
  END,
  NUMBER,
  PLUS,
  MINUS,
  MUL,
  DIV,
  POW,
  LPAREN,
  RPAREN,
  BAD
} TokenType;

typedef struct Parser {
  const char* text;
  size_t length;
  size_t cursor;
  size_t file_offset;
  size_t token_position;
  size_t error_position;
  TokenType token;
  Value value;
} Parser;

typedef struct Options {
  const char* input_file;
  const char* input_directory;
  const char* output_directory;
} Options;

static void* allocate_memory(size_t size);
static void set_error(Parser* parser, size_t position);
static Value make_integer(long long number);
static double as_double(Value value);
static long long integer_power(long long base, unsigned long long exponent);
static void next_token(Parser* parser);
static Value parse_primary(Parser* parser);
static Value calculate(Parser* parser, TokenType operator_type, Value left, Value right, size_t operator_position, size_t right_position);
static Value parse_power(Parser* parser);
static Value parse_term(Parser* parser);
static Value parse_expression(Parser* parser);
static char* join_path(const char* directory, const char* filename);
static char* get_base_name(const char* path, int strip_txt);
static char* create_output_path(const char* input_path, const char* output_directory);
static int evaluate_line(const char* line, size_t length, size_t file_offset, FILE* results, size_t* error_position);
static int copy_results(FILE* results, FILE* output);
static int write_output(const char* input_path, const char* output_directory, FILE* results, size_t error_position);
static int process_file(const char* input_path, const char* output_directory);
static int process_directory(const char* input_directory, const char* output_directory);
static int read_arguments(int argc, char** argv, Options* options);
static int validate_input(const Options* options);
static char* create_default_directory(const Options* options);
static int prepare_output_directory(const char* directory_name);

static void* allocate_memory(size_t size) {
  if (size == 0) {
    size = 1;
  }

  void* memory = malloc(size);
  if (memory == NULL) {
    fprintf(stderr, "out of memory\n");
    exit(EXIT_FAILURE);
  }

  return memory;
}

static void set_error(Parser* parser, size_t position) {
  if (!parser->error_position) {
    parser->error_position = position;
  }
}

static Value make_integer(long long number) {
  Value value = {0};
  value.integer_value = number;
  value.is_float = 0;
  return value;
}

static double as_double(Value value) {
  if (value.is_float) {
    return value.float_value;
  }

  return (double)value.integer_value;
}

static long long integer_power(long long base, unsigned long long exponent) {
  long long result = 1;

  while (exponent > 0) {
    if (exponent % 2 == 1) {
      result = result * base;
    }

    exponent = exponent / 2;

    if (exponent > 0) {
      base = base * base;
    }
  }

  return result;
}

static void next_token(Parser* parser) {
  size_t start;
  while (parser->cursor < parser->length &&
         (parser->text[parser->cursor] == ' ' ||
          parser->text[parser->cursor] == '\t')) {
    ++parser->cursor;
  }
  start = parser->cursor;

  parser->token_position = parser->file_offset + start + 1;
  if (start == parser->length) {
    parser->token = END;
    return;
  }
  unsigned char character = (unsigned char)parser->text[parser->cursor];
  parser->cursor++;
  if (isdigit(character)) {
    while (parser->cursor < parser->length &&
           isdigit((unsigned char)parser->text[parser->cursor])) {
      ++parser->cursor;
    }
    int floating = 0;
    if (parser->cursor < parser->length &&
        parser->text[parser->cursor] == '.') {
      size_t dot = parser->cursor;
      parser->cursor++;
      if (parser->cursor == parser->length ||
          !isdigit((unsigned char)parser->text[parser->cursor])) {
        parser->token = BAD;
        parser->token_position = parser->file_offset + dot + 1;
        return;
      }
      floating = 1;
      while (parser->cursor < parser->length &&
             isdigit((unsigned char)parser->text[parser->cursor])) {
        ++parser->cursor;
      }
    }
    size_t n = parser->cursor - start;
    char* number = allocate_memory(n + 1);
    memcpy(number, parser->text + start, n);
    number[n] = '\0';
    parser->value = make_integer(0);
    parser->value.is_float = floating;
    errno = 0;
    if (floating) {
      parser->value.float_value = strtod(number, NULL);
    } else {
      parser->value.integer_value = strtoll(number, NULL, 10);
    }
    free(number);
    parser->token = NUMBER;
    if (errno == ERANGE || (floating && !isfinite(parser->value.float_value))) {
      parser->token = BAD;
    }
    return;
  }
  switch (character) {
    case '+':
      parser->token = PLUS;
      break;
    case '-':
      parser->token = MINUS;
      break;
    case '/':
      parser->token = DIV;
      break;
    case '(':
      parser->token = LPAREN;
      break;
    case ')':
      parser->token = RPAREN;
      break;
    case '*':
      if (parser->cursor < parser->length &&
          parser->text[parser->cursor] == '*') {
        ++parser->cursor;
        parser->token = POW;
      } else {
        parser->token = MUL;
      }
      break;
    default:
      parser->token = BAD;
      break;
  }
}

static Value parse_primary(Parser* parser) {
  Value result = make_integer(0);
  if (parser->error_position) {
    return result;
  }
  if (parser->token == NUMBER) {
    result = parser->value;
    next_token(parser);
  } else if (parser->token == LPAREN) {
    next_token(parser);
    result = parse_expression(parser);
    if (!parser->error_position) {
      if (parser->token != RPAREN) {
        set_error(parser, parser->token_position);
      } else {
        next_token(parser);
      }
    }
  } else {
    set_error(parser, parser->token_position);
  }
  return result;
}

static Value calculate(Parser* parser, TokenType operator_type, Value left, Value right, size_t operator_position, size_t right_position) {
  if (parser->error_position) {
    return make_integer(0);
  }
  if (operator_type == DIV && as_double(right) == 0.0) {
    set_error(parser, right_position);
    return make_integer(0);
  }
  if (left.is_float || right.is_float) {
    Value result = {0, 0.0, 1};
    double left_number = as_double(left), right_number = as_double(right);
    switch (operator_type) {
      case PLUS:
        result.float_value = left_number + right_number;
        break;
      case MINUS:
        result.float_value = left_number - right_number;
        break;
      case MUL:
        result.float_value = left_number * right_number;
        break;
      case DIV:
        result.float_value = left_number / right_number;
        break;
      default:
        result.float_value = pow(left_number, right_number);
        break;
    }
    if (!isfinite(result.float_value)) {
      set_error(parser, operator_position);
    }
    return result;
  }
  switch (operator_type) {
    case PLUS:
      return make_integer(left.integer_value + right.integer_value);
    case MINUS:
      return make_integer(left.integer_value - right.integer_value);
    case MUL:
      return make_integer(left.integer_value * right.integer_value);
    case DIV:
      return make_integer(left.integer_value / right.integer_value);
    default: {
      if (right.integer_value < 0) {
        set_error(parser, right_position);
        return make_integer(0);
      }
      unsigned long long exponent = (unsigned long long)right.integer_value;
      long long result = integer_power(left.integer_value, exponent);
      return make_integer(result);
    }
  }
}

static Value parse_power(Parser* parser) {
  Value left = parse_primary(parser);
  if (!parser->error_position && parser->token == POW) {
    size_t operator_position = parser->token_position;
    next_token(parser);
    size_t right_position = parser->token_position;

    Value right = parse_power(parser);
    left =
        calculate(parser, POW, left, right, operator_position, right_position);
  }
  return left;
}

static Value parse_term(Parser* parser) {
  Value left = parse_power(parser);

  while (!parser->error_position &&
         (parser->token == MUL || parser->token == DIV)) {
    TokenType operator_type = parser->token;
    size_t operator_position = parser->token_position;
    next_token(parser);
    size_t right_position = parser->token_position;
    Value right = parse_power(parser);
    left = calculate(parser, operator_type, left, right, operator_position,
                     right_position);
  }
  return left;
}

static Value parse_expression(Parser* parser) {
  Value left = parse_term(parser);
  while (!parser->error_position &&
         (parser->token == PLUS || parser->token == MINUS)) {
    TokenType operator_type = parser->token;
    size_t operator_position = parser->token_position;
    next_token(parser);
    size_t right_position = parser->token_position;
    Value right = parse_term(parser);
    left = calculate(parser, operator_type, left, right, operator_position,
                     right_position);
  }
  return left;
}

static char* join_path(const char* directory, const char* filename) {
  size_t directory_length = strlen(directory);
  size_t filename_length = strlen(filename);
  size_t size = directory_length + filename_length + 2;
  char* path = allocate_memory(size);

  snprintf(path, size, "%s/%s", directory, filename);
  return path;
}

static char* get_base_name(const char* path, int strip_txt) {
  size_t end = strlen(path);

  while (end > 1 && path[end - 1] == '/') {
    end--;
  }

  size_t start = end;
  while (start > 0 && path[start - 1] != '/') {
    start--;
  }

  size_t length = end - start;
  if (strip_txt && length >= 4 && memcmp(path + end - 4, ".txt", 4) == 0) {
    length = length - 4;
  }

  if (length == 0) {
    char* name = allocate_memory(6);
    memcpy(name, "input", 6);
    return name;
  }

  char* name = allocate_memory(length + 1);
  memcpy(name, path + start, length);
  name[length] = '\0';
  return name;
}

static char* create_output_path(const char* input_path, const char* output_directory) {
  char* base_name = get_base_name(input_path, 1);
  size_t size = strlen(base_name) + strlen(FIRST_NAME) + strlen(LAST_NAME) + strlen(STUDENT_ID) + 8;
  char* filename = allocate_memory(size);

  snprintf(filename, size, "%s_%s_%s_%s.txt", base_name, FIRST_NAME, LAST_NAME, STUDENT_ID);

  char* output_path = join_path(output_directory, filename);
  free(filename);
  free(base_name);
  return output_path;
}

static int evaluate_line(const char* line, size_t length, size_t file_offset, FILE* results, size_t* error_position) {
  size_t first = 0;

  while (first < length && (line[first] == ' ' || line[first] == '\t')) {
    first++;
  }

  if (first == length || line[first] == '#') {
    return 1;
  }

  Parser parser = {0};
  parser.text = line;
  parser.length = length;
  parser.file_offset = file_offset;

  next_token(&parser);
  Value result = parse_expression(&parser);

  if (parser.error_position == 0 && parser.token != END) {
    set_error(&parser, parser.token_position);
  }

  *error_position = parser.error_position;
  if (*error_position != 0) {
    return 1;
  }

  int written;
  if (result.is_float) {
    written = fprintf(results, "%.15g\n", result.float_value);
  } else {
    written = fprintf(results, "%lld\n", result.integer_value);
  }

  return written >= 0;
}

static int copy_results(FILE* results, FILE* output) {
  if (fflush(results) != 0) {
    return 0;
  }

  if (fseek(results, 0, SEEK_SET) != 0) {
    return 0;
  }

  char buffer[8192];
  size_t count = fread(buffer, 1, sizeof(buffer), results);

  while (count > 0) {
    if (fwrite(buffer, 1, count, output) != count) {
      return 0;
    }
    count = fread(buffer, 1, sizeof(buffer), results);
  }

  return !ferror(results);
}

static int write_output(const char* input_path, const char* output_directory, FILE* results, size_t error_position) {
  char* output_path = create_output_path(input_path, output_directory);
  FILE* output = fopen(output_path, "wb");

  if (output == NULL) {
    fprintf(stderr, "cannot write %s: %s\n", output_path, strerror(errno));
    free(output_path);
    return 0;
  }

  int success;
  if (error_position != 0) {
    success = fprintf(output, "ERROR:%zu\n", error_position) >= 0;
  } else {
    success = copy_results(results, output);
  }

  if (fclose(output) != 0) {
    success = 0;
  }

  free(output_path);
  return success;
}

static int process_file(const char* input_path, const char* output_directory) {
  FILE* input = fopen(input_path, "rb");
  if (input == NULL) {
    fprintf(stderr, "cannot read %s: %s\n", input_path, strerror(errno));
    return 0;
  }

  FILE* results = tmpfile();
  if (results == NULL) {
    fprintf(stderr, "cannot create temporary file\n");
    fclose(input);
    return 0;
  }

  char* line = NULL;
  size_t capacity = 0;
  size_t length = 0;
  size_t file_offset = 0;
  size_t error_position = 0;
  int success = 1;

  while (1) {
    int character = fgetc(input);

    if (character != '\n' && character != EOF) {
      if (length == capacity) {
        size_t new_capacity = 256;
        if (capacity > 0) {
          new_capacity = capacity * 2;
        }

        char* larger_buffer = realloc(line, new_capacity);
        if (larger_buffer == NULL) {
          fprintf(stderr, "out of memory\n");
          success = 0;
          break;
        }

        line = larger_buffer;
        capacity = new_capacity;
      }

      line[length] = (char)character;
      length++;
      continue;
    }

    success =
        evaluate_line(line, length, file_offset, results, &error_position);
    if (!success || error_position != 0) {
      break;
    }

    file_offset = file_offset + length;
    if (character == '\n') {
      file_offset++;
    }
    length = 0;

    if (character == EOF) {
      break;
    }
  }

  if (ferror(input)) {
    fprintf(stderr, "read error: %s\n", input_path);
    success = 0;
  }
  if (fclose(input) != 0) {
    success = 0;
  }
  free(line);

  if (success) {
    success =
        write_output(input_path, output_directory, results, error_position);
  }
  if (fclose(results) != 0) {
    success = 0;
  }
  if (!success) {
    fprintf(stderr, "failed processing %s\n", input_path);
  }

  return success;
}

static int process_directory(const char* input_directory, const char* output_directory) {
  DIR* directory = opendir(input_directory);
  if (directory == NULL) {
    fprintf(stderr, "cannot open directory: %s\n", input_directory);
    return 0;
  }

  int success = 1;

  while (1) {
    errno = 0;
    struct dirent* entry = readdir(directory);

    if (entry == NULL) {
      if (errno != 0) {
        fprintf(stderr, "cannot read directory: %s\n", input_directory);
        success = 0;
      }
      break;
    }

    size_t name_length = strlen(entry->d_name);
    if (name_length < 4) {
      continue;
    }
    if (strcmp(entry->d_name + name_length - 4, ".txt") != 0) {
      continue;
    }

    char* input_path = join_path(input_directory, entry->d_name);
    struct stat information;

    if (stat(input_path, &information) != 0) {
      fprintf(stderr, "cannot inspect %s\n", input_path);
      success = 0;
    } else if (S_ISREG(information.st_mode)) {
      if (!process_file(input_path, output_directory)) {
        success = 0;
      }
    }

    free(input_path);
  }

  if (closedir(directory) != 0) {
    success = 0;
  }

  return success;
}

static int read_arguments(int argc, char** argv, Options* options) {
  for (int index = 1; index < argc; index++) {
    const char* argument = argv[index];

    if (strcmp(argument, "-d") == 0 || strcmp(argument, "--dir") == 0) {
      if (options->input_directory != NULL || index + 1 == argc) {
        return 0;
      }
      if (argv[index + 1][0] == '-') {
        return 0;
      }
      index++;
      options->input_directory = argv[index];
    } else if (strcmp(argument, "-o") == 0 ||
               strcmp(argument, "--output-dir") == 0) {
      if (options->output_directory != NULL || index + 1 == argc) {
        return 0;
      }
      if (argv[index + 1][0] == '-') {
        return 0;
      }
      index++;
      options->output_directory = argv[index];
    } else {
      if (argument[0] == '-' || options->input_file != NULL) {
        return 0;
      }
      options->input_file = argument;
    }
  }

  if (options->input_file == NULL && options->input_directory == NULL) {
    return 0;
  }
  if (options->input_file != NULL && options->input_directory != NULL) {
    return 0;
  }

  return 1;
}

static int validate_input(const Options* options) {
  const char* input_path = options->input_file;
  if (options->input_directory != NULL) {
    input_path = options->input_directory;
  }

  struct stat information;
  if (stat(input_path, &information) != 0) {
    fprintf(stderr, "cannot inspect input: %s\n", input_path);
    return 0;
  }

  int valid;
  if (options->input_directory != NULL) {
    valid = S_ISDIR(information.st_mode);
  } else {
    valid = S_ISREG(information.st_mode);
  }

  if (!valid) {
    fprintf(stderr, "invalid input type: %s\n", input_path);
  }
  return valid;
}

static char* create_default_directory(const Options* options) {
  const char* input_path = options->input_file;
  int strip_txt = 1;

  if (options->input_directory != NULL) {
    input_path = options->input_directory;
    strip_txt = 0;
  }

  char* base_name = get_base_name(input_path, strip_txt);
  size_t size = strlen(base_name) + strlen(FIRST_NAME) + strlen(STUDENT_ID) + 3;
  char* directory_name = allocate_memory(size);

  snprintf(directory_name, size, "%s_%s_%s", base_name, FIRST_NAME, STUDENT_ID);
  free(base_name);
  return directory_name;
}

static int prepare_output_directory(const char* directory_name) {
  if (mkdir(directory_name, 0777) != 0 && errno != EEXIST) {
    fprintf(stderr, "cannot create output directory: %s\n", directory_name);
    return 0;
  }

  struct stat information;
  if (stat(directory_name, &information) != 0) {
    fprintf(stderr, "cannot inspect output directory: %s\n", directory_name);
    return 0;
  }
  if (!S_ISDIR(information.st_mode)) {
    fprintf(stderr, "output path is not a directory: %s\n", directory_name);
    return 0;
  }

  return 1;
}

int main(int argc, char** argv) {
  Options options = {0};

  if (!read_arguments(argc, argv, &options)) {
    fprintf(stderr,
            "usage: %s [-d DIR | --dir DIR] "
            "[-o OUTDIR | --output-dir OUTDIR] [input.txt]\n",
            argv[0]);
    return EXIT_FAILURE;
  }

  if (!validate_input(&options)) {
    return EXIT_FAILURE;
  }

  char* default_directory = NULL;
  if (options.output_directory == NULL) {
    default_directory = create_default_directory(&options);
    options.output_directory = default_directory;
  }

  if (!prepare_output_directory(options.output_directory)) {
    free(default_directory);
    return EXIT_FAILURE;
  }

  int success;
  if (options.input_file != NULL) {
    success = process_file(options.input_file, options.output_directory);
  } else {
    success = process_directory(options.input_directory, options.output_directory);
  }

  free(default_directory);

  if (!success) {
    return EXIT_FAILURE;
  }

  return EXIT_SUCCESS;
}