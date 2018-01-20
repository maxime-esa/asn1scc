WORD_SIZE = 8


class bitarray:
    __native__ = True  # to check if native bitarray implementation is used

    def __init__(self, source=None):
        self._data = bytearray()
        self._bitsize = 0

        if self.__iterable_bits(source):
            self._init_from_iterable(source)

        elif isinstance(source, int) and source > 0:
            self._init_from_size(source)

    def frombytes(self, source):
        self._init_from_bytes(source)

    def _init_from_size(self, size):
        self._data = bytearray(self.get_byte_length_from_bit_length(size))
        self._bitsize = size

    def _init_from_iterable(self, source):
        self.__append_bits(source)

    def _init_from_bytes(self, source):
        self._data = bytearray(source)
        self._bitsize = len(self._data) * WORD_SIZE

    def set_size(self, new_size):
        self._bitsize = new_size

    def __getitem__(self, item):
        if isinstance(item, slice):
            return self.__get_slice(item)

        self.__assert_correct_index(item)

        bit_position = self.__get_bit_position(item)
        byte_position = self.__get_byte_position(item)

        byte = self._data[byte_position]
        byte >>= bit_position
        bit = byte & 0b00000001

        return bit

    def __get_slice(self, item):
        start = item.start or 0
        if start < 0:
            start = self._bitsize + start

        elif start >= self._bitsize:
            start = self._bitsize - 1

        stop = item.stop or self._bitsize
        if stop < 0:
            stop = self._bitsize + stop

        elif stop >= self._bitsize:
            stop = self._bitsize

        return bitarray([self[i] for i in range(start, stop, item.step or 1)])

    def __setitem__(self, item, value):
        self.__assert_correct_index(item)
        self.__assert_bit(value)

        bit_position = self.__get_bit_position(item)
        byte_position = self.__get_byte_position(item)

        byte = self._data[byte_position]
        byte = self.__set_bit(byte, bit_position) if int(value) else self.__clear_bit(byte, bit_position)
        self._data[byte_position] = byte

    def __delitem__(self, item):
        self.__assert_correct_index(item)

        for i in range(item, self._bitsize - 1):
            self[i] = self[i + 1]

        self[self._bitsize - 1] = 0
        self._bitsize -= 1

    def __add__(self, other):
        if self.is_bit(other):
            self.append_bit(int(other))

        elif isinstance(other, bytes):
            for byte in other:
                self.append_byte(byte)

        elif self.__iterable_bits(other):
            self.__append_bits(other)

        else:
            raise TypeError("Can't add '{}' to bitarray implicitly".format(other))

        return self

    def __eq__(self, other):
        for i, b in enumerate(self):
            if str(b) != str(other[i]):
                return False

        return True

    def __iter__(self):
        self._n = 0
        return self

    def __next__(self):
        if self._n < self._bitsize:
            element = self[self._n]
            self._n += 1
            return element

        else:
            raise StopIteration

    def __len__(self):
        return self._bitsize

    def __repr__(self):
        return str([bit for bit in self])

    def to01(self):
        return str(self)

    def __str__(self):
        return ''.join([str(bit) for bit in self])

    def __getattr__(self, item):
        raise AttributeError("'bitarray' object has no attribute '{}'".format(item))

    def append(self, bit):
        self.append_bit(bit)

    def append_bit(self, bit):
        self.__assert_bit(bit)

        if self._bitsize & (WORD_SIZE - 1):
            byte = self._data[-1]
            bit_position = self.__get_bit_position(self._bitsize)
            self._data[-1] = self.__set_bit(byte, bit_position) if int(bit) else self.__clear_bit(byte, bit_position)

        else:
            byte = 0b10000000 if int(bit) else 0b00000000
            self._data.append(byte)

        self._bitsize += 1

    def append_byte(self, byte):
        if self._bitsize & (WORD_SIZE - 1):
            old_byte = self._data.pop()
            bit_position = self.__get_bit_position(self._bitsize)
            old_byte |= byte >> (WORD_SIZE - bit_position - 1)
            self._data.append(old_byte)
            self._data.append((byte << (bit_position + 1)) & 0b11111111)

        else:
            self._data.append(byte)

        self._bitsize += WORD_SIZE

    def insert(self, index, value):
        self.__assert_correct_index(index)
        self.__assert_bit(value)

        self.append_bit(0)

        for i in range(self._bitsize - 1, index, -1):
            self[i] = self[i - 1]

        self[index] = int(value)

    def pop(self, index=None):
        index = index or self._bitsize - 1
        self.__assert_correct_index(index)

        bit = self[index]
        del self[index]

        return bit

    def remove(self, index=None):
        index = index or self._bitsize - 1
        self.__assert_correct_index(index)

        del self[index]

        return self

    def reverse(self):
        new = self.copy()

        for i, b in enumerate(self):
            new[self._bitsize - i - 1] = b

        return new

    def clear(self):
        self._data = bytearray()
        self._bitsize = 0

    def tobytes(self):
        return self._data

    def copy(self):
        return bitarray(self)

    def extend(self, other):
        if self.__iterable_bits(other):
            self.__append_bits(other)

    def length(self):
        return self._bitsize

    @classmethod
    def fromhex(cls, s):
        return bitarray(bytearray.fromhex(s))

    def hex(self):
        return self._data.hex()

    def __append_bits(self, bit_iterable):
        for c in bit_iterable:
            self.append_bit(int(c))

    @staticmethod
    def __iterable_bits(source):
        return hasattr(source, '__iter__') and all([bitarray.is_bit(c) for c in source])

    def __assert_correct_index(self, item):
        if 0 <= item >= self._bitsize:
            raise AttributeError("Item {} doesn't exist!".format(item))

    @staticmethod
    def __assert_bit(value):
        if not bitarray.is_bit(value):
            raise AttributeError("bitarray can't contain {} value".format(value))

    @staticmethod
    def __get_byte_position(position):
        return position // WORD_SIZE

    @staticmethod
    def __get_bit_position(position):
        return WORD_SIZE - (position & (WORD_SIZE - 1)) - 1

    @staticmethod
    def __set_bit(byte, bit):
        return byte | (1 << bit)

    @staticmethod
    def __clear_bit(byte, bit):
        return byte & ~(1 << bit)

    @staticmethod
    def is_bit(c):
        return str(int(c)) in ['0', '1']

    @staticmethod
    def get_byte_length_from_bit_length(bit_length):
        return (bit_length + WORD_SIZE - 1) // WORD_SIZE
