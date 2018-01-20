from unittest import TestCase

import asn1


class BitStreamTest(TestCase):
    def setUp(self):
        self.b = asn1.BitStream()

    def test_append_read_bit(self):
        self.b.append_bit(1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.read_bit())

    def test_append_read_byte(self):
        self.b.append_byte(123)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123, self.b2.read_byte())

    def test_append_read_byte_negate(self):
        self.b.append_byte(~(-200), True)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(56, self.b2.read_byte())

    def test_append_read_partial_byte(self):
        self.b.append_partial_byte(0b10100101, 3)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0b10100000, self.b2.read_partial_byte(3))

    def test_append_read_partial_byte_negate(self):
        self.b.append_partial_byte(0b10100101, 3, True)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0b01000000, self.b2.read_partial_byte(3))

    def test_append_read_bits(self):
        self.b.append_bits(bytearray([0b10100101, 0b11001100]), 9)
        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(bytearray([0b10100101, 0b10000000]), self.b2.read_bits(9))

    def test_read_bit_pattern(self):
        self.b.append_bits(bytearray([0b10100101, 0b11001100, 0b11101111]), 20)

        self.b2 = asn1.BitStream(self.b)
        self.assertTrue(self.b2.read_bit_pattern(bytearray([0b10100101, 0b11001100, 0b11101111]), 10))

    def test_encode_decode_non_negative_integer32_0(self):
        self.b.encode_non_negative_integer32(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.decode_non_negative_integer32(0))

    def test_encode_decode_non_negative_integer32_little(self):
        self.b.encode_non_negative_integer32(33)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(33, self.b2.decode_non_negative_integer32(6))

    def test_encode_decode_non_negative_integer32_medium(self):
        self.b.encode_non_negative_integer32(321)
        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(321, self.b2.decode_non_negative_integer32(int(321).bit_length()))

    def test_encode_decode_non_negative_integer32_big(self):
        self.b.encode_non_negative_integer32(3217)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(3217, self.b2.decode_non_negative_integer32(int(3217).bit_length()))

    def test_encode_decode_non_negative_integer32_plus_max(self):
        self.b.encode_non_negative_integer32(asn1.INT_MAX)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.decode_non_negative_integer32(int(asn1.INT_MAX).bit_length()))

    def test_encode_decode_non_negative_integer_plus_max(self):
        self.b.encode_non_negative_integer(asn1.INT_MAX)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.decode_non_negative_integer(int(asn1.INT_MAX).bit_length()))

    def test_encode_decode_non_negative_integer_more(self):
        self.b.encode_non_negative_integer(0x1ffffffff)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x1ffffffff, self.b2.decode_non_negative_integer(int(0x1ffffffff).bit_length()))

    def test_encode_decode_constraint_number_0(self):
        self.b.encode_constraint_number(0, 0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.decode_constraint_number(0, 0))

    def test_encode_decode_constraint_number_little(self):
        self.b.encode_constraint_number(5, 1, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(5, self.b2.decode_constraint_number(1, 10))

    def test_encode_decode_constraint_number_medium(self):
        self.b.encode_constraint_number(1234, 12, 2342)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.decode_constraint_number(12, 2342))

    def test_encode_decode_constraint_number_big(self):
        self.b.encode_constraint_number(123433, 1222, 234211)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123433, self.b2.decode_constraint_number(1222, 234211))

    def test_encode_decode_constraint_number_big_little_range(self):
        self.b.encode_constraint_number(234210, 234209, 234211)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(234210, self.b2.decode_constraint_number(234209, 234211))
        self.assertEqual(2, self.b._current_bit)

    def test_encode_decode_semi_constraint_number_0(self):
        self.b.encode_semi_constraint_number(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.decode_semi_constraint_number(0))

    def test_encode_decode_semi_constraint_number_little(self):
        self.b.encode_semi_constraint_number(23, 2)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(23, self.b2.decode_semi_constraint_number(2))

    def test_encode_decode_semi_constraint_number_medium(self):
        self.b.encode_semi_constraint_number(12345, 432)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(12345, self.b2.decode_semi_constraint_number(432))

    def test_encode_decode_semi_constraint_number_big(self):
        self.b.encode_semi_constraint_number(234234234, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(234234234, self.b2.decode_semi_constraint_number(0))

    def test_encode_decode_semi_constraint_number_big_little_semi(self):
        self.b.encode_semi_constraint_number(234234234, 234234233)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(234234234, self.b2.decode_semi_constraint_number(234234233))

    def test_encode_decode_number_0(self):
        self.b.encode_number(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.decode_number())

    def test_encode_decode_number_1(self):
        self.b.encode_number(1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.decode_number())

    def test_encode_decode_number_127(self):
        self.b.encode_number(127)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(127, self.b2.decode_number())

    def test_encode_decode_number_255(self):
        self.b.encode_number(255)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(255, self.b2.decode_number())

    def test_encode_decode_number_256(self):
        self.b.encode_number(256)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(256, self.b2.decode_number())

    def test_encode_decode_number_12345(self):
        self.b.encode_number(12345)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(12345, self.b2.decode_number())

    def test_encode_decode_number_max(self):
        self.b.encode_number(asn1.INT_MAX)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.decode_number())

    def test_encode_decode_number_minus_1(self):
        self.b.encode_number(-1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1, self.b2.decode_number())

    def test_encode_decode_number_minus_127(self):
        self.b.encode_number(-127)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-127, self.b2.decode_number())

    def test_encode_decode_number_minus_255(self):
        self.b.encode_number(-255)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-255, self.b2.decode_number())

    def test_encode_decode_number_minus_256(self):
        self.b.encode_number(-256)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-256, self.b2.decode_number())

    def test_encode_decode_number_minus_12345(self):
        self.b.encode_number(-12345)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-12345, self.b2.decode_number())

    def test_encode_decode_number_minus_max(self):
        self.b.encode_number(asn1.INT_MIN)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MIN, self.b2.decode_number())

    def test_encode_decode_real_0(self):
        self.b.encode_real(0.0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0.0, self.b2.decode_real())

    def test_encode_decode_real_1_234(self):
        self.b.encode_real(1.234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1.234, self.b2.decode_real())

    def test_encode_decode_real_0_5(self):
        self.b.encode_real(0.5)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0.5, self.b2.decode_real())

    def test_encode_decode_real_16(self):
        self.b.encode_real(16)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(16, self.b2.decode_real())

    def test_encode_decode_real_int_max(self):
        self.b.encode_real(asn1.INT_MAX)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(float(asn1.INT_MAX), self.b2.decode_real(), delta=0.001)

    def test_encode_decode_real_minus_1_234(self):
        self.b.encode_real(-1.234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1.234, self.b2.decode_real())

    def test_encode_decode_real_minus_0_5(self):
        self.b.encode_real(-0.5)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0.5, self.b2.decode_real())

    def test_encode_decode_real_minus_16(self):
        self.b.encode_real(-16)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-16, self.b2.decode_real())

    def test_encode_decode_real_int_min(self):
        self.b.encode_real(asn1.INT_MIN)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(float(asn1.INT_MIN), self.b2.decode_real(), delta=0.001)

    def test_encode_decode_real_inf(self):
        self.b.encode_real(asn1.INFINITY)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INFINITY, self.b2.decode_real())

    def test_encode_decode_real_minus_inf(self):
        self.b.encode_real(-asn1.INFINITY)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-asn1.INFINITY, self.b2.decode_real())

    # acn

    def test_integer_size_bcd(self):
        self.assertEqual(self.b.acn_get_integer_size_bcd(123456789), 9)

    def test_integer_size_ascii(self):
        self.assertEqual(self.b.acn_get_integer_size_ascii(-123456789), 10)

    def test_acn_encode_decode_positive_integer_const_size_0_0(self):
        self.b.acn_encode_positive_integer_const_size(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size(0))

    def test_acn_encode_decode_positive_integer_const_size_1_1(self):
        self.b.acn_encode_positive_integer_const_size(1, 1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.acn_decode_positive_integer_const_size(1))

    def test_acn_encode_decode_positive_integer_const_size_1_10(self):
        self.b.acn_encode_positive_integer_const_size(1, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.acn_decode_positive_integer_const_size(10))

    def test_acn_encode_decode_positive_integer_const_size_255_10(self):
        self.b.acn_encode_positive_integer_const_size(255, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(255, self.b2.acn_decode_positive_integer_const_size(10))

    def test_acn_encode_decode_positive_integer_const_size_max_10(self):
        max_10_bits = asn1.INT_MAX >> asn1.INT_MAX.bit_length() - 10
        self.b.acn_encode_positive_integer_const_size(max_10_bits, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(max_10_bits, self.b2.acn_decode_positive_integer_const_size(10))

    def test_acn_encode_decode_positive_integer_const_size_max_max(self):
        self.b.acn_encode_positive_integer_const_size(asn1.INT_MAX, asn1.INT_MAX.bit_length())

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.acn_decode_positive_integer_const_size(asn1.INT_MAX.bit_length()))

    def test_acn_encode_decode_positive_integer_const_size_8_0(self):
        self.b.acn_encode_positive_integer_const_size_8(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_8())

    def test_acn_encode_decode_positive_integer_const_size_8_123(self):
        self.b.acn_encode_positive_integer_const_size_8(123)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123, self.b2.acn_decode_positive_integer_const_size_8())

    def test_acn_encode_decode_positive_integer_const_size_8_255(self):
        self.b.acn_encode_positive_integer_const_size_8(255)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(255, self.b2.acn_decode_positive_integer_const_size_8())

    def test_acn_encode_decode_positive_integer_const_size_16_0_big(self):
        self.b.acn_encode_positive_integer_const_size_16_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_16_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_16_0_little(self):
        self.b.acn_encode_positive_integer_const_size_16_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_16_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_16_1234_big(self):
        self.b.acn_encode_positive_integer_const_size_16_big_endian(1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.acn_decode_positive_integer_const_size_16_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_16_1234_little(self):
        self.b.acn_encode_positive_integer_const_size_16_little_endian(1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.acn_decode_positive_integer_const_size_16_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_16_face_big(self):
        self.b.acn_encode_positive_integer_const_size_16_big_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_positive_integer_const_size_16_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_16_face_little(self):
        self.b.acn_encode_positive_integer_const_size_16_little_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_positive_integer_const_size_16_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_0_big(self):
        self.b.acn_encode_positive_integer_const_size_32_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_32_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_0_little(self):
        self.b.acn_encode_positive_integer_const_size_32_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_32_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_face_big(self):
        self.b.acn_encode_positive_integer_const_size_32_big_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_positive_integer_const_size_32_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_face_little(self):
        self.b.acn_encode_positive_integer_const_size_32_little_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_positive_integer_const_size_32_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_f0a0c0e0_big(self):
        self.b.acn_encode_positive_integer_const_size_32_big_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_positive_integer_const_size_32_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_32_f0a0c0e0_little(self):
        self.b.acn_encode_positive_integer_const_size_32_little_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_positive_integer_const_size_32_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_0_big(self):
        self.b.acn_encode_positive_integer_const_size_64_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_64_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_0_little(self):
        self.b.acn_encode_positive_integer_const_size_64_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_const_size_64_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_f0a0c0e0_big(self):
        self.b.acn_encode_positive_integer_const_size_64_big_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_positive_integer_const_size_64_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_f0a0c0e0_little(self):
        self.b.acn_encode_positive_integer_const_size_64_little_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_positive_integer_const_size_64_little_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_f0a0c0e0f0a0c0e0_big(self):
        self.b.acn_encode_positive_integer_const_size_64_big_endian(0xF0A0C0E0F0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0F0A0C0E0, self.b2.acn_decode_positive_integer_const_size_64_big_endian())

    def test_acn_encode_decode_positive_integer_const_size_64_f0a0c0e0f0a0c0e0_little(self):
        self.b.acn_encode_positive_integer_const_size_64_little_endian(0xF0A0C0E0F0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0F0A0C0E0, self.b2.acn_decode_positive_integer_const_size_64_little_endian())

    def test_acn_encode_decode_positive_integer_var_size_length_embedded_0(self):
        self.b.acn_encode_positive_integer_var_size_length_embedded(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_positive_integer_var_size_length_embedded())

    def test_acn_encode_decode_positive_integer_var_size_length_embedded_max(self):
        self.b.acn_encode_positive_integer_var_size_length_embedded(asn1.INT_MAX)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.acn_decode_positive_integer_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_const_size_0_0(self):
        self.b.acn_encode_integer_twos_complement_const_size(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size(0))

    def test_acn_encode_decode_integer_twos_complement_const_size_1_2(self):
        self.b.acn_encode_integer_twos_complement_const_size(1, 2)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.acn_decode_integer_twos_complement_const_size(2))

    def test_acn_encode_decode_integer_twos_complement_const_size_minus_1_2(self):
        self.b.acn_encode_integer_twos_complement_const_size(-1, 2)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1, self.b2.acn_decode_integer_twos_complement_const_size(2))

    def test_acn_encode_decode_integer_twos_complement_const_size_1_10(self):
        self.b.acn_encode_integer_twos_complement_const_size(1, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_minus_6_10(self):
        self.b.acn_encode_integer_twos_complement_const_size(-6, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-6, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_255_10(self):
        self.b.acn_encode_integer_twos_complement_const_size(255, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(255, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_minus_255_10(self):
        self.b.acn_encode_integer_twos_complement_const_size(-255, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-255, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_max_10(self):
        max_10_bits = asn1.INT_MAX >> asn1.INT_MAX.bit_length() - 9
        self.b.acn_encode_integer_twos_complement_const_size(max_10_bits, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(max_10_bits, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_minus_max_10(self):
        max_10_bits = asn1.INT_MAX >> asn1.INT_MAX.bit_length() - 9
        self.b.acn_encode_integer_twos_complement_const_size(-max_10_bits, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-max_10_bits, self.b2.acn_decode_integer_twos_complement_const_size(10))

    def test_acn_encode_decode_integer_twos_complement_const_size_max_max(self):
        bit_length = asn1.INT_MAX.bit_length()
        self.b.acn_encode_integer_twos_complement_const_size(asn1.INT_MAX, bit_length + 1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(asn1.INT_MAX, self.b2.acn_decode_integer_twos_complement_const_size(bit_length + 1))

    def test_acn_encode_decode_integer_twos_complement_const_size_8_0(self):
        self.b.acn_encode_integer_twos_complement_const_size_8(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_8())

    def test_acn_encode_decode_integer_twos_complement_const_size_8_123(self):
        self.b.acn_encode_integer_twos_complement_const_size_8(123)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123, self.b2.acn_decode_integer_twos_complement_const_size_8())

    def test_acn_encode_decode_integer_twos_complement_const_size_8_minus_16(self):
        self.b.acn_encode_integer_twos_complement_const_size_8(-16)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-16, self.b2.acn_decode_integer_twos_complement_const_size_8())

    def test_acn_encode_decode_integer_twos_complement_const_size_8_127(self):
        self.b.acn_encode_integer_twos_complement_const_size_8(127)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(127, self.b2.acn_decode_integer_twos_complement_const_size_8())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_16_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_16_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_1234_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_big_endian(1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.acn_decode_integer_twos_complement_const_size_16_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_1234_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_little_endian(1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.acn_decode_integer_twos_complement_const_size_16_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_minus_1234_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_big_endian(-1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1234, self.b2.acn_decode_integer_twos_complement_const_size_16_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_minus_1234_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_little_endian(-1234)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1234, self.b2.acn_decode_integer_twos_complement_const_size_16_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_face_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_big_endian(0x7ACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x7ACE, self.b2.acn_decode_integer_twos_complement_const_size_16_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_16_face_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_16_little_endian(0x7ACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x7ACE, self.b2.acn_decode_integer_twos_complement_const_size_16_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_32_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_32_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_face_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_big_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_integer_twos_complement_const_size_32_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_face_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_little_endian(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_integer_twos_complement_const_size_32_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_minus_face_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_big_endian(-0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0xFACE, self.b2.acn_decode_integer_twos_complement_const_size_32_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_minus_face_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_little_endian(-0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0xFACE, self.b2.acn_decode_integer_twos_complement_const_size_32_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_f0a0c0e0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_big_endian(0x70A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x70A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_32_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_32_f0a0c0e0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_32_little_endian(0x70A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x70A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_32_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_64_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_const_size_64_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_f0a0c0e0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_big_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_f0a0c0e0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_little_endian(0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xF0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_minus_f0a0c0e0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_big_endian(-0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0xF0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_minus_f0a0c0e0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_little_endian(-0xF0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0xF0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_little_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_f0a0c0e0f0a0c0e0_big(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_big_endian(0x70A0C0E0F0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x70A0C0E0F0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_big_endian())

    def test_acn_encode_decode_integer_twos_complement_const_size_64_f0a0c0e0f0a0c0e0_little(self):
        self.b.acn_encode_integer_twos_complement_const_size_64_little_endian(0x70A0C0E0F0A0C0E0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0x70A0C0E0F0A0C0E0, self.b2.acn_decode_integer_twos_complement_const_size_64_little_endian())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_0(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_1(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_255(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(255)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(255, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_minus_255(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(-255)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-255, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_face(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0xFACE, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_twos_complement_var_size_length_embedded_minus_face(self):
        self.b.acn_encode_integer_twos_complement_var_size_length_embedded(-0xFACE)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-0xFACE, self.b2.acn_decode_integer_twos_complement_var_size_length_embedded())

    def test_acn_encode_decode_integer_bcd_const_size_0(self):
        self.b.acn_encode_integer_bcd_const_size(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_bcd_const_size(0))

    def test_acn_encode_decode_integer_bcd_const_size_12345_5(self):
        self.b.acn_encode_integer_bcd_const_size(12345, 5)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(12345, self.b2.acn_decode_integer_bcd_const_size(5))

    def test_acn_encode_decode_integer_bcd_const_size_90876543021_5(self):
        self.b.acn_encode_integer_bcd_const_size(90876543021, 11)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(90876543021, self.b2.acn_decode_integer_bcd_const_size(11))

    def test_acn_encode_decode_integer_bcd_var_size_length_embedded_0(self):
        self.b.acn_encode_integer_bcd_var_size_length_embedded(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_bcd_var_size_length_embedded())

    def test_acn_encode_decode_integer_bcd_var_size_length_embedded_9090(self):
        self.b.acn_encode_integer_bcd_var_size_length_embedded(9090)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(9090, self.b2.acn_decode_integer_bcd_var_size_length_embedded())

    def test_acn_encode_decode_integer_bcd_var_size_length_embedded_1234567890(self):
        self.b.acn_encode_integer_bcd_var_size_length_embedded(1234567890)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234567890, self.b2.acn_decode_integer_bcd_var_size_length_embedded())

    def test_acn_encode_decode_integer_bcd_var_size_null_terminated_0(self):
        self.b.acn_encode_integer_bcd_var_size_null_terminated(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_integer_bcd_var_size_null_terminated())

    def test_acn_encode_decode_integer_bcd_var_size_null_terminated_123456789(self):
        self.b.acn_encode_integer_bcd_var_size_null_terminated(123456789)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123456789, self.b2.acn_decode_integer_bcd_var_size_null_terminated())

    def test_acn_encode_decode_unsigned_integer_ascii_const_size_0(self):
        self.b.acn_encode_unsigned_integer_ascii_const_size(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_unsigned_integer_ascii_const_size(0))

    def test_acn_encode_decode_unsigned_integer_ascii_const_size_1234567890(self):
        self.b.acn_encode_unsigned_integer_ascii_const_size(1234567890, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234567890, self.b2.acn_decode_unsigned_integer_ascii_const_size(10))

    def test_acn_encode_decode_signed_integer_ascii_const_size_0(self):
        self.b.acn_encode_signed_integer_ascii_const_size(0, 1)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_signed_integer_ascii_const_size(0))

    def test_acn_encode_decode_signed_integer_ascii_const_size_1234567890(self):
        self.b.acn_encode_signed_integer_ascii_const_size(1234567890, 11)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234567890, self.b2.acn_decode_signed_integer_ascii_const_size(11))

    def test_acn_encode_decode_signed_integer_ascii_const_size_minus_1234567890(self):
        self.b.acn_encode_signed_integer_ascii_const_size(-1234567890, 11)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(-1234567890, self.b2.acn_decode_signed_integer_ascii_const_size(11))

    def test_acn_encode_decode_unsigned_integer_ascii_var_size_length_embedded_0(self):
        self.b.acn_encode_unsigned_integer_ascii_var_size_length_embedded(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_unsigned_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_unsigned_integer_ascii_var_size_length_embedded_9090(self):
        self.b.acn_encode_unsigned_integer_ascii_var_size_length_embedded(9090)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(9090, self.b2.acn_decode_unsigned_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_unsigned_integer_ascii_var_size_length_embedded_1234567890(self):
        self.b.acn_encode_unsigned_integer_ascii_var_size_length_embedded(1234567890)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234567890, self.b2.acn_decode_unsigned_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_signed_integer_ascii_var_size_length_embedded_0(self):
        self.b.acn_encode_signed_integer_ascii_var_size_length_embedded(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_signed_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_signed_integer_ascii_var_size_length_embedded_9090(self):
        self.b.acn_encode_signed_integer_ascii_var_size_length_embedded(9090)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(9090, self.b2.acn_decode_signed_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_signed_integer_ascii_var_size_length_embedded_1234567890(self):
        self.b.acn_encode_signed_integer_ascii_var_size_length_embedded(1234567890)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234567890, self.b2.acn_decode_signed_integer_ascii_var_size_length_embedded())

    def test_acn_encode_decode_unsigned_integer_ascii_var_size_null_terminated_0(self):
        self.b.acn_encode_unsigned_integer_ascii_var_size_null_terminated(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_unsigned_integer_ascii_var_size_null_terminated())

    def test_acn_encode_decode_unsigned_integer_ascii_var_size_null_terminated_123456789(self):
        self.b.acn_encode_unsigned_integer_ascii_var_size_null_terminated(123456789)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123456789, self.b2.acn_decode_unsigned_integer_ascii_var_size_null_terminated())

    def test_acn_encode_decode_signed_integer_ascii_var_size_null_terminated_0(self):
        self.b.acn_encode_signed_integer_ascii_var_size_null_terminated(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_signed_integer_ascii_var_size_null_terminated())

    def test_acn_encode_decode_signed_integer_ascii_var_size_null_terminated_123456789(self):
        self.b.acn_encode_signed_integer_ascii_var_size_null_terminated(123456789)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(123456789, self.b2.acn_decode_signed_integer_ascii_var_size_null_terminated())

    def test_acn_encode_decode_real_big_endian_0(self):
        self.b.acn_encode_real_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_real_big_endian())

    def test_acn_encode_decode_real_big_endian_1_123(self):
        self.b.acn_encode_real_big_endian(1.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(1.123, self.b2.acn_decode_real_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_big_endian_123_123(self):
        self.b.acn_encode_real_big_endian(123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123.123, self.b2.acn_decode_real_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_big_endian_minus_123_123(self):
        self.b.acn_encode_real_big_endian(-123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123.123, self.b2.acn_decode_real_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_big_endian_0(self):
        self.b.acn_encode_real_ieee745_32_big_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_real_ieee745_32_big_endian())

    def test_acn_encode_decode_real_ieee745_32_big_endian_1_123(self):
        self.b.acn_encode_real_ieee745_32_big_endian(1.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(1.123, self.b2.acn_decode_real_ieee745_32_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_big_endian_123_123(self):
        self.b.acn_encode_real_ieee745_32_big_endian(123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123.123, self.b2.acn_decode_real_ieee745_32_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_big_endian_minus_123_123(self):
        self.b.acn_encode_real_ieee745_32_big_endian(-123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123.123, self.b2.acn_decode_real_ieee745_32_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_64_big_endian_123_123(self):
        self.b.acn_encode_real_ieee745_64_big_endian(123234456567.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123234456567.123, self.b2.acn_decode_real_ieee745_64_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_64_big_endian_minus_123_123(self):
        self.b.acn_encode_real_ieee745_64_big_endian(-123234456567.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123234456567.123, self.b2.acn_decode_real_ieee745_64_big_endian(), delta=0.00001)

    def test_acn_encode_decode_real_little_endian_0(self):
        self.b.acn_encode_real_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_real_little_endian())

    def test_acn_encode_decode_real_little_endian_1_123(self):
        self.b.acn_encode_real_little_endian(1.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(1.123, self.b2.acn_decode_real_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_little_endian_123_123(self):
        self.b.acn_encode_real_little_endian(123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123.123, self.b2.acn_decode_real_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_little_endian_minus_123_123(self):
        self.b.acn_encode_real_little_endian(-123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123.123, self.b2.acn_decode_real_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_little_endian_0(self):
        self.b.acn_encode_real_ieee745_32_little_endian(0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_real_ieee745_32_little_endian())

    def test_acn_encode_decode_real_ieee745_32_little_endian_1_123(self):
        self.b.acn_encode_real_ieee745_32_little_endian(1.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(1.123, self.b2.acn_decode_real_ieee745_32_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_little_endian_123_123(self):
        self.b.acn_encode_real_ieee745_32_little_endian(123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123.123, self.b2.acn_decode_real_ieee745_32_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_32_little_endian_minus_123_123(self):
        self.b.acn_encode_real_ieee745_32_little_endian(-123.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123.123, self.b2.acn_decode_real_ieee745_32_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_64_little_endian_123_123(self):
        self.b.acn_encode_real_ieee745_64_little_endian(123234456567.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(123234456567.123, self.b2.acn_decode_real_ieee745_64_little_endian(), delta=0.00001)

    def test_acn_encode_decode_real_ieee745_64_little_endian_minus_123_123(self):
        self.b.acn_encode_real_ieee745_64_little_endian(-123234456567.123)

        self.b2 = asn1.BitStream(self.b)
        self.assertAlmostEqual(-123234456567.123, self.b2.acn_decode_real_ieee745_64_little_endian(), delta=0.00001)

    def test_acn_encode_decode_string_ascii_fix_size_empty(self):
        self.b.acn_encode_string_ascii_fix_size('')

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_ascii_fix_size(0))

    def test_acn_encode_decode_string_ascii_fix_size_a(self):
        self.b.acn_encode_string_ascii_fix_size('a')

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('a', self.b2.acn_decode_string_ascii_fix_size(1))

    def test_acn_encode_decode_string_ascii_fix_size_lorem_ipsum(self):
        self.b.acn_encode_string_ascii_fix_size('Lorem ipsum')

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_ascii_fix_size(11))

    def test_acn_encode_decode_string_ascii_fix_size_123(self):
        self.b.acn_encode_string_ascii_fix_size('123')

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('123', self.b2.acn_decode_string_ascii_fix_size(3))

    def test_acn_encode_decode_string_ascii_null_terminated_empty(self):
        self.b.acn_encode_string_ascii_null_terminated('', 0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_ascii_null_terminated(0, 1))

    def test_acn_encode_decode_string_ascii_null_terminated_lorem_ipsum(self):
        self.b.acn_encode_string_ascii_null_terminated('Lorem ipsum', 0, 12)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_ascii_null_terminated(0, 12))

    def test_acn_encode_decode_string_ascii_null_terminated_lorem_ipsum_null_e(self):
        self.b.acn_encode_string_ascii_null_terminated('Lorem ipsum', ord('e'), 11)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lor', self.b2.acn_decode_string_ascii_null_terminated(ord('e'), 11))

    def test_acn_encode_decode_string_ascii_external_field_determinant_empty(self):
        self.b.acn_encode_string_ascii_external_field_determinant('', 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_ascii_external_field_determinant(0, 0))

    def test_acn_encode_decode_string_ascii_external_field_determinant_lorem_ipsum(self):
        self.b.acn_encode_string_ascii_external_field_determinant('Lorem ipsum', 100)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_ascii_external_field_determinant(11, 100))

    def test_acn_encode_decode_string_ascii_internal_field_determinant_empty(self):
        self.b.acn_encode_string_ascii_internal_field_determinant('', 0, 100)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_ascii_internal_field_determinant(0, 100))

    def test_acn_encode_decode_string_ascii_internal_field_determinant_lorem_ipsum(self):
        self.b.acn_encode_string_ascii_internal_field_determinant('Lorem ipsum', 0, 100)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_ascii_internal_field_determinant(0, 100))

    def test_acn_encode_decode_string_char_index_fix_size_empty(self):
        self.b.acn_encode_string_char_index_fix_size('', "")

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_char_index_fix_size(0, ""))

    def test_acn_encode_decode_string_char_index_fix_size_a(self):
        self.b.acn_encode_string_char_index_fix_size('a', "abcd")

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('a', self.b2.acn_decode_string_char_index_fix_size(1, "abcd"))

    def test_acn_encode_decode_string_char_index_fix_size_lorem_ipsum(self):
        self.b.acn_encode_string_char_index_fix_size(
            'Lorem ipsum', "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz "
        )

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_char_index_fix_size(
            11, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz "
        ))

    def test_acn_encode_decode_string_char_index_fix_size_123(self):
        self.b.acn_encode_string_char_index_fix_size('123', "123")

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('123', self.b2.acn_decode_string_char_index_fix_size(3, "123"))

    def test_acn_encode_decode_string_char_index_external_field_determinant_empty(self):
        self.b.acn_encode_string_char_index_external_field_determinant('', "", 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_char_index_external_field_determinant(0, "", 0))

    def test_acn_encode_decode_string_char_index_external_field_determinant_lorem_ipsum(self):
        self.b.acn_encode_string_char_index_external_field_determinant(
            'Lorem ipsum', "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz ", 100
        )

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_char_index_external_field_determinant(
            11, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz ", 11
        ))

    def test_acn_encode_decode_string_char_index_internal_field_determinant_empty(self):
        self.b.acn_encode_string_char_index_internal_field_determinant('', "", 0, 100)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('', self.b2.acn_decode_string_char_index_internal_field_determinant("", 0, 100))

    def test_acn_encode_decode_string_char_index_internal_field_determinant_lorem_ipsum(self):
        self.b.acn_encode_string_char_index_internal_field_determinant(
            'Lorem ipsum', "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz ", 0, 100
        )

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual('Lorem ipsum', self.b2.acn_decode_string_char_index_internal_field_determinant(
            "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz ", 0, 100
        ))

    def test_acn_encode_decode_length_0_0(self):
        self.b.acn_encode_length(0, 0)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_length(0))

    def test_acn_encode_decode_length_0_10(self):
        self.b.acn_encode_length(0, 10)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(0, self.b2.acn_decode_length(10))

    def test_acn_encode_decode_length_1234_10(self):
        self.b.acn_encode_length(1234, 16)

        self.b2 = asn1.BitStream(self.b)
        self.assertEqual(1234, self.b2.acn_decode_length(16))
