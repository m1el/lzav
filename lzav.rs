/**
 * lzav.h version 2.15
 *
 * The inclusion file for the "LZAV" in-memory data compression and
 * decompression algorithms.
 *
 * Description is available at https://github.com/avaneev/lzav
 * E-mail: aleksey.vaneev@gmail.com or info@voxengo.com
 *
 * License
 *
 * Copyright (c) 2023 Aleksey Vaneev
 * Copyright (c) 2023 Igor null <m1el.2027@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
extern crate core;
use core::mem::size_of;
use core::convert::TryInto;

pub const LZAV_API_VER: usize = 0x101; // API version, unrelated to code's version.


/// Decompression error codes:
#[repr(i32)]
#[derive(Debug)]
pub enum LZAVError {
	EParams = -1, // Incorrect function parameters.
	SrcOob = -2, // Source buffer OOB.
	DstOob = -3, // Destination buffer OOB.
	RefOob = -4, // Back-reference OOB.
	DstLen = -5, // Decompressed length mismatch.
	UnkFmt = -6, // Unknown stream format.
}

// NOTE: all macros defined below are for internal use, do not change.

/// LZ77 window length, in bytes.
const LZAV_WIN_LEN: usize = 1 << 24; 
/// Max literal length, in bytes.
const LZAV_LIT_LEN: usize = 1 + 15 + 255 + 255; 
/// Min reference length, in bytes.
const LZAV_REF_MIN: usize = 6; 
/// Max reference length.
const LZAV_REF_LEN: usize = LZAV_REF_MIN + 15 + 255;
/// The number of literals required at finish.
const LZAV_LIT_FIN: usize = 5;
/// Stream format identifier used by the compressor.
const LZAV_FMT_CUR: usize = 1;

/**
 * Function finds the number of continuously-matching leading bytes between
 * two buffers. This function is well-optimized for a wide variety of
 * compilers and platforms.
 *
 * @param p1 Pointer to buffer 1.
 * @param p2 Pointer to buffer 2.
 * @param ml Maximal number of bytes to match.
 * @return The number of matching leading bytes.
 */
fn lzav_match_len(p1: &[u8], p2: &[u8]) -> usize {
	let min_len = p1.len().min(p2.len());
	for ii in 0..min_len {
		if p1[ii] != p2[ii] {
			return ii;
		}
	}
	min_len
}

/**
 * Internal function writes a block to the output buffer. This function can be
 * used in custom compression algorithms.
 *
 * Stream format 1.
 *
 * "Raw" compressed stream consists of any quantity of unnumerated "blocks".
 * A block starts with a header byte, followed by several optional bytes.
 * Bits 4-5 of the header specify block's type.
 *
 * CC00LLLL: literal block (1-3 bytes). LLLL is literal length.
 * OO01RRRR: 10-bit offset block (2-3 bytes). RRRR is reference length.
 * OO10RRRR: 18-bit offset block (3-4 bytes).
 * CC11RRRR: 24-bit offset block (4-5 bytes).
 *
 * If LLLL==0 or RRRR==0, a value of 16 is assumed, and an additional length
 * byte follows. If in a literal block this additional byte is equal to 255,
 * one more length byte follows. In a reference block, an additional length
 * byte follows the offset bytes. CC is a reference offset carry value
 * (additional 2 lowest bits of offset of the next reference block).
 *
 * The overall compressed data is prefixed with a byte whose lower 4 bits
 * contain minimal reference length (mref), and the highest 4 bits contain
 * stream format identifier. Compressed data always finishes with
 * LZAV_LIT_LEN literals. The lzav_write_fin_1() function should be used to
 * finalize compression.
 *
 * @param op Output buffer pointer.
 * @param lc Literal length, in bytes.
 * @param rc Reference length, in bytes, not lesser than mref.
 * @param d Reference offset, in bytes. Should be lesser than LZAV_WIN_LEN,
 * and not lesser than rc since fast copy on decompression cannot provide
 * consistency of copying of data that is not in the output yet.
 * @param ipa Literals anchor pointer.
 * @param cbpp Pointer to the pointer to the latest offset carry block header.
 * Cannot be 0, but the contained pointer can be 0.
 * @param mref Minimal reference length, in bytes, used by the compression
 * algorithm.
 * @return Incremented output buffer pointer.
 */
fn lzav_write_blk_1(
	op: &mut Vec<u8>,
	mut ipa: &[u8],
	mut d: usize,
	mut rc: usize,
	mref: usize,
	cbpp: &mut Option<usize>,
) {
	while ipa.len() > LZAV_LIT_LEN {
		op.push(0);
		op.push(255);
		op.push(255);
		op.extend_from_slice(&ipa[..LZAV_LIT_LEN]);
		ipa = &ipa[LZAV_LIT_LEN..];
	}

	if !ipa.is_empty() {
		// Write literal block.
		let cv = (d & 3) << 6;
		d >>= 2;
		*cbpp = None;
		if ipa.len() < 9 {
			op.push((cv | ipa.len()) as u8);
		} else if ipa.len() < 1 + 15 {
			op.push((cv | ipa.len()) as u8);
		} else if ipa.len() < 1 + 15 + 255 {
			let ov = ((ipa.len() - 1 - 15) << 8 | cv) as u16;
			op.extend_from_slice(&ov.to_le_bytes());
		} else {
			let il = (ipa.len() - 1 - 15 - 255) as u8;
			op.extend_from_slice(&[cv as u8, 255, il]);
		}
		op.extend_from_slice(ipa);
	} else {
		if let Some(cbp) = cbpp.take() {
			// Perform offset carry to a previous block header.
			op[cbp] |= (d << 6) as u8;
			d >>= 2;
		}
	}

	// Write reference block.

	rc = rc + 1 - mref;
	if d < (1 << 10) {
		if rc < 16 {
			let ov = ((d << 6) | (1 << 4) | rc ) as u16;
			op.extend_from_slice(&ov.to_le_bytes());
			return;
		} else {
			op.push((d << 6 | 1 << 4) as u8);
			let ov = (((rc - 16) << 8) | (d >> 2)) as u16;
			op.extend_from_slice(&ov.to_le_bytes());
			return;
		}
	}
	if d < (1 << 18) {
		if rc < 16 {
			op.push(((d << 6) | (2 << 4) | rc) as u8);
			let ov = (d >> 2) as u16;
			op.extend_from_slice(&ov.to_le_bytes());
			return;
		} else {
			let ov = (((rc - 16) << 24) | (d << 6) | (2 << 4)) as u32;
			op.extend_from_slice(&ov.to_le_bytes());
			return;
		}
	}
	*cbpp = Some(op.len());
	if rc < 16 {
		let ov = ((d << 8) | (3 << 4) | rc) as u32;
		op.extend_from_slice(&ov.to_le_bytes());
		return;
	}
	op.push(3 << 4);
	let ov = (((rc - 16) << 24) | d) as u32;
	op.extend_from_slice(&ov.to_le_bytes())
}

/**
 * Internal function writes finishing literal block(s) to the output buffer.
 * This function can be used in custom compression algorithms.
 *
 * Stream format 1.
 *
 * @param op Output buffer pointer.
 * @param lc Literal length, in bytes. Not less than LZAV_LIT_FIN.
 * @param ipa Literals anchor pointer.
 * @return Incremented output buffer pointer.
 */
fn lzav_write_fin_1(op: &mut Vec<u8>, mut ipa: &[u8]) {
	while ipa.len() > 15 {
		// Leave literals for the final block.
		let mut wc = ipa.len() - LZAV_LIT_FIN;
		if wc < 1 + 15 {
			op.push(wc as u8);
		} else {
			if wc > LZAV_LIT_LEN {
				wc = LZAV_LIT_LEN;
			}
			if wc < 1 + 15 + 255 {
				op.extend_from_slice(&[
					0,
					(wc - 1 - 15) as u8,
				]);
			} else {
				op.extend_from_slice(&[
					0,
					255,
					(wc - 1 - 15 - 255) as u8,
				]);
			}
		}
		op.extend_from_slice(&ipa[..wc]);
		ipa = &ipa[wc..];
	}
	op.push(ipa.len() as u8);
	op.extend_from_slice(ipa);
}

/**
 * @param srcl The length of the source data to be compressed.
 * @return The required allocation size for destination compression buffer.
 * Always a positive value.
 */
fn lzav_compress_bound(srcl: usize) -> usize {
	if srcl <= 0 {
		8
	} else {
		srcl + srcl * 3 / LZAV_LIT_LEN + 8
	}
}

#[derive(Clone,Debug)]
struct HTEntry {
	val1: [u8; 4],
	off1: u32,
	val2: [u8; 4],
	off2: u32,
}

/**
 * Function performs in-memory data compression using the LZAV compression
 * algorithm and stream format. The function produces a "raw" compressed data,
 * without a header containing data length nor identifier nor checksum.
 *
 * Note that compression algorithm and its output on the same source data may
 * differ between LZAV versions, and may differ on little- and big-endian
 * systems. However, the decompression of a compressed data produced by any
 * prior compressor version will stay possible.
 *
 * @param[in] src Source (uncompressed) data pointer, can be 0 if srcl==0.
 * Address alignment is unimportant.
 * @param[out] dst Destination (compressed data) buffer pointer. The allocated
 * size should be at least lzav_compress_bound() bytes large. Address
 * alignment is unimportant. Should be different to src.
 * @param srcl Source data length, in bytes, can be 0: in this case the
 * compressed length is assumed to be 0 as well.
 * @param dstl Destination buffer's capacity, in bytes.
 * @param ext_buf External buffer to use for hash-table, set to 0 for the
 * function to manage memory itself (via std malloc). Supplying a
 * pre-allocated buffer is useful if compression is performed during
 * application's operation often: this reduces memory allocation overhead and
 * fragmentation. Note that the access to the supplied buffer is not
 * implicitly thread-safe.
 * @param ext_bufl The capacity of the ext_buf, in bytes, should be a
 * power-of-2 value. Set to 0 if ext_buf is 0. The capacity should not be
 * lesser than 4*srcl, not lesser than 256, but not greater than 1
 * MiB. Same ext_bufl value can be used for any smaller sources.
 * @return The length of compressed data, in bytes. Returns 0 if srcl<=0, or
 * if dstl is too small, or if not enough memory.
 */
fn lzav_compress(
	src: &[u8],
	dst: &mut Vec<u8>,
	ht: &mut Vec<HTEntry>,
) {
	dst.clear();
	if src.is_empty() {
		return;
	}
	dst.reserve(lzav_compress_bound(src.len()));
	let srcl = src.len();
	if srcl <= LZAV_LIT_FIN {
		// Handle a very short source data.
		dst.push((LZAV_FMT_CUR << 4 | LZAV_REF_MIN) as u8);
		dst.push(src.len() as u8);
		dst.extend_from_slice(src);
		dst.resize_with(LZAV_LIT_FIN + 2, || 0);
		return;
	}

	// Hash-table's capacity (power-of-2).
	let mut htcap = 1 << 8; 

	while htcap < (1 << 16) && htcap * 4 < srcl {
		htcap <<= 1;
	}

	let htsize = htcap * size_of::<u32>() * 4;
	let hmask = ((htsize - 1) ^ 0xf) as u32;

	let mut ip = 0;
	let ipe = srcl.saturating_sub(LZAV_LIT_FIN); // End pointer.
	let ipet = ipe.saturating_sub(LZAV_REF_MIN - 1); // Hashing threshold.
	let mut ipa = ip; // Literals anchor pointer.
	let op = dst; // Destination (compressed data) pointer.
	let mut cbp: Option<usize> = None; // Pointer to the latest offset carry block header.
	let mut mavg = 100 << 22; // Running average of hash match rate (*2^16).
		// Two-factor average: success (0-64) by average reference length.
	let mut rndb = 0; // PRNG bit derived from the non-matching offset.
	ip += LZAV_REF_MIN; // Skip source bytes, to avoid OOB in rc2 match below.
	op.push((LZAV_FMT_CUR << 4 | LZAV_REF_MIN) as u8);  // Write prefix byte.
	// Initialize the hash-table. Each hash-table item consists of 2 tuples
	// (4 initial match bytes; 32-bit source data offset). Set source data
	// offset to avoid rc2 OOB below.


	assert!(size_of::<HTEntry>() == 4 * 4);
	let mut first = [0; 4];
	if ip < ipet {
		first.copy_from_slice(&src[ip..ip+4]);
	}
	let htinit = HTEntry {
		val1: first,
		off1: LZAV_REF_MIN as u32,
		val2: first,
		off2: LZAV_REF_MIN as u32,
	};
	ht.clear();
	ht.extend((0..htcap).map(|_| htinit.clone()));

	while ip < ipet {
		// hd(&op);
		// println!("---");
		// Hash source data (endianness is unimportant for compression
		// efficiency). Hash is based on the "komihash" math construct, see
		// https://github.com/avaneev/komihash for details.
		let word_0_4: [u8; 4] = src[ip..ip+4].try_into().unwrap();
		let word_4_6: [u8; 2] = src[ip+4..ip+6].try_into().unwrap();
		let seed1 = 0x243F6A88 ^ u32::from_ne_bytes(word_0_4);
		let hm = seed1 as u64 * (0x85A308D3 ^ u16::from_ne_bytes(word_4_6) as u64);
		let hval = (hm ^ (hm >> 32)) as u32;

		// Hash-table access.
		let ipo = ip;
		let ht_index = ((hval & hmask) >> 4) as usize;
		let hp = &mut ht[ht_index];

		// Find source data in hash-table tuples.
		let mut wp = None;
		let mut wpo = 0;
		let mut ww2: [u8; 2];
		if word_0_4 == hp.val1 {
			wpo = hp.off1 as usize;
			wp = Some(wpo);
			ww2 = src[wpo+4..wpo+6].try_into().unwrap();
			let hp2 = hp.val2;
			if word_4_6 != ww2 {
				if word_0_4 != hp2 {
					hp.val2 = word_0_4;
					hp.off2 = ipo as u32;
					wp = None;
				} else {
					wpo = hp.off2 as usize;
					ww2 = src[wpo+4..wpo+6].try_into().unwrap();
					if word_4_6 != ww2 {
						hp.val1 = word_0_4;
						hp.off1 = ipo as u32;
						wp = None;
					}
				}
			}
		} else {
			if word_0_4 != hp.val2 {
				hp.val2 = word_0_4;
				hp.off2 = ipo as u32;
			} else {
				wpo = hp.off2 as usize;
				wp = Some(wpo);
				ww2 = src[wpo+4..wpo+6].try_into().unwrap();
				if word_4_6 != ww2 {
					hp.val1 = word_0_4;
					hp.off1 = ipo as u32;
					wp = None;
				}
			}
		}

		let wp = if let Some(has) = wp {
			has
		} else {
			mavg -= mavg >> 11;

			if mavg < (200 << 15) && ip != ipa {
				// Compression speed-up technique that keeps the number of
				// hash evaluations around 45% of compressed data length.
				// In some cases reduces the number of blocks by several
				// percent.

				ip += 2 | rndb; // Use PRNG bit to dither match positions.
				rndb = ipo & 1; // Delay to decorrelate from current match.

				if mavg < 130 << 15 {
					ip += 1;

					if mavg < 100 << 15 {
						ip += 100 - ( mavg >> 15 ); // Gradually faster.
					}
				}

				continue;
			}

			ip += 1;
			continue;
		};

		let d = ipo - wpo; // Reference offset.

		if (d <= 7) | (d >= LZAV_WIN_LEN) {
			// Small offsets may be inefficient.

			if d >= LZAV_WIN_LEN {
				if word_0_4 != hp.val1 {
					hp.off2 = ipo as u32;
				} else {
					hp.off2 = ipo as u32;
				}
			}

			ip += 1;
			continue;
		}

		// Source data and hash-table entry match.
		if d > LZAV_REF_LEN {
			// Update a matching entry which is not inside max reference
			// length's range. Otherwise, source data consisting of same-byte
			// runs won't compress well.

			let hp0 = hp.val1;

			if word_0_4 != hp0 { // Insert tuple, or replace.
				hp.val2 = hp0;
				hp.off2 = hp.off1;
				hp.val1 = word_0_4;
			}

			hp.off1 = ipo as u32;
		}

		// Disallow overlapped reference copy.
		let mut ml = d.min(LZAV_REF_LEN);

		if ip + ml > ipe {
			// Make sure LZAV_LIT_FIN literals remain on finish.
			ml = ipe - ip;
		}

		let mut lc = ip - ipa;
		let mut rc = 0;

		if lc != 0 && lc < LZAV_REF_MIN {
			// Try to consume literals by finding a match at an earlier
			// position.

			let a = &src[ip - lc..][..ml];
			let b = &src[wp - lc..][..ml];
			let rc2 = lzav_match_len(a, b);

			if rc2 >= LZAV_REF_MIN {
				rc = rc2;
				ip -= lc;
				lc = 0;
			}
		}

		if rc == 0 {
			let a = &src[ip + LZAV_REF_MIN..ip + ml];
			let b = &src[wp + LZAV_REF_MIN..ip + ml];
			rc = LZAV_REF_MIN + lzav_match_len(a, b);
		}
		let sipa = &src[ipa..][..lc];
		lzav_write_blk_1(op, sipa, d, rc, LZAV_REF_MIN, &mut cbp);
		ip += rc;
		ipa = ip;
		mavg += ((rc << 22 ) - mavg) >> 10;
	}
	lzav_write_fin_1(op, &src[ipa..]);
}

/**
 * Function performs in-memory data compression using the LZAV compression
 * algorithm, with the default settings.
 *
 * See the lzav_compress() function for more detailed description.
 *
 * @param[in] src Source (uncompressed) data pointer.
 * @param[out] dst Destination (compressed data) buffer pointer. The allocated
 * size should be at least lzav_compress_bound() bytes large.
 * @param srcl Source data length, in bytes.
 * @param dstl Destination buffer's capacity, in bytes.
 * @return The length of compressed data, in bytes. Returns 0 if srcl<=0, or
 * if dstl is too small, or if not enough memory.
 */
fn lzav_compress_default(src: &[u8], dst: &mut Vec<u8>) {
	lzav_compress(src, dst, &mut Vec::new());
}

/**
 * Function decompresses "raw" data previously compressed into the LZAV stream
 * format. Stream format 1.
 *
 * Note that while the function does perform checks to avoid OOB memory
 * accesses, and checks for decompressed data length equality, this is not a
 * strict guarantee of a valid decompression. In cases when the compressed
 * data is stored in a long-term storage without embedded data integrity
 * mechanisms (e.g., a database without RAID 0 guarantee, a binary container
 * without a digital signature nor CRC), a checksum (hash) of the original
 * uncompressed data should be stored, and then evaluated against that of the
 * decompressed data. Also, a separate checksum (hash) of application-defined
 * header, which contains uncompressed and compressed data lengths, should be
 * checked before decompression. A high-performance "komihash" hash function
 * can be used to obtain a hash value of the data.
 *
 * @param[in] src Source (compressed) data pointer, can be 0 if srcl==0.
 * Address alignment is unimportant.
 * @param[out] dst Destination (decompressed data) buffer pointer. Address
 * alignment is unimportant. Should be different to src.
 * @param srcl Source data length, in bytes, can be 0.
 * @param dstl Expected destination data length, in bytes, can be 0.
 * @return The length of decompressed data, in bytes, or any negative value if
 * some error happened. Always returns a negative value if the resulting
 * decompressed data length differs from dstl. This means that error result
 * handling requires just a check for a negative return value (see the
 * LZAV_E_x macros for possible values).
 */

fn lzav_decompress(src: &[u8], dst: &mut Vec<u8>, dstl: usize) -> Result<(), LZAVError> {
	let srcl = src.len();
	dst.clear();
	if srcl == 0 {
		if dstl == 0 {
			return Ok(());
		} else {
			return Err(LZAVError::EParams);
		}
	}

	if dstl == 0 {
		return Err(LZAVError::EParams);
	}

	if src[0] >> 4 != 1 {
		return Err(LZAVError::UnkFmt);
	}
	dst.reserve(dstl);

	let mut ip = 0; // Compressed data pointer.
	let ipe = ip + srcl; // End pointer.
	let ipet = ipe - 5; // Header read threshold LZAV_LIT_FIN.
	let op = dst; // Destination (decompressed data) pointer.
	let ope = dstl; // Destination boundary pointer.
	let opet = ope.saturating_sub(63); // Threshold for fast copy to destination.
	let mref1 = (( src[ip] & 15 ) - 1) as usize; // Minimal reference length - 1.
	let mut bh = 0; // Current block header, updated in each branch.
	let mut cv = 0; // Reference offset carry value.
	let mut csh = 0; // Reference offset carry shift.

	ip += 1;
	if ip < ipet {
		bh = src[ip] as usize;
	}

	macro_rules! load {
		($ty:ident, $ip:expr) => {
			$ty::from_le_bytes(src[$ip..][..size_of::<$ty>()].try_into().unwrap())
		}
	}

	while ip < ipet {
		if (bh & 0x30) == 0 { // Block type 0.
			let mut ipd; // Source data pointer.
			cv = (bh >> 6) as usize;
			csh = 2;
			let mut cc = (bh & 15) as usize; // Byte copy count.
			let orig_len = op.len();
			if cc != 0 { // True, if no additional length byte.
				ip += 1;
				ipd = ip;
				ip += cc;

				if ip < ipe {
					bh = src[ip] as usize;

					if (op.len() < opet) & (ipd + 15 < ipe) {
						op.extend_from_slice(&src[ipd..][..16]);
						op.truncate(orig_len + cc);
						continue;
					}
				} else {
					if ip > ipe {
						return Err(LZAVError::SrcOob);
					}

					if (op.len() < opet) & (ipd + 15 < ipe) {
						op.extend_from_slice(&src[ipd..][..16]);
						op.truncate(orig_len + cc);
						continue;
					}
				}
			} else {
				let bv = load!(u16, ip+1) as usize;
				let l2 = (bv & 0xff) as usize;
				let lb = (l2 == 255) as usize;
				cc = 16 + l2 + ((bv >> 8) & (0x100 - lb));
				ip += 2 + lb;
				ipd = ip;
				ip += cc;

				if ip < ipe {
					bh = src[ip] as usize;
				} else if ip > ipe {
					return Err(LZAVError::SrcOob);
				}

				if (op.len() < opet) & (ipd + 63 < ipe) {
					op.extend_from_slice(&src[ipd..][..64]);

					if cc <= 64 {
						op.truncate(orig_len + cc);
						continue;
					}

					ipd += 64;
					cc -= 64;
				}
			}

			if  op.len() + cc > ope {
				return Err(LZAVError::DstOob);
			}

			if cc > 0 {
				op.extend_from_slice(&src[ipd..][..cc]);
			}

			continue;
		}
		let mut cc = bh & 15; // Byte copy count.

		let mut ipd; // Reference data pointer.
		macro_rules! set_ipd_cv {
			($x:expr, $v:expr, $sh:expr) => {
				let d = $x << csh | cv;
				if d > op.len() {
					return Err(LZAVError::RefOob);
				}
				ipd = op.len() - d;
				cv = $v;
				csh = $sh;
			}
		}
		macro_rules! set_ipd {
			($x:expr) => {
				set_ipd_cv!($x, 0, 0);
			}
		}
		fn mem_move<const N: usize>(vec: &mut Vec<u8>, off: usize) {
			let mut buf = [0; N];
			buf.copy_from_slice(&vec[off..][..N]);
			vec.extend_from_slice(&buf);
		}
		if cc != 0 { // True, if no additional length byte.
			cc += mref1;

			if (bh & 32) != 0 { // True, if block type 2 or 3.
				if (bh & 16) == 0 { // True, if block type 2.
					let bv = load!(u16, ip + 1) as usize;
					set_ipd!((bh >> 6) | (bv << 2));
					ip += 3;
					bh = src[ip] as usize;

					let orig_len = op.len();
					if op.len() < opet {
						mem_move::<32>(op, ipd);
						op.truncate(orig_len + cc);
						continue;
					}
				} else { // Block type 3.
					let bv = load!(u32, ip + 1) as usize;
					set_ipd_cv!(bv & 0xFFFFFF, bh >> 6, 2);
					ip += 4;
					bh = bv >> 24;
					let orig_len = op.len();
					if op.len() < opet {
						mem_move::<32>(op, ipd);
						op.truncate(orig_len + cc);
						continue;
					}
				}
			} else { // Block type 1.
				set_ipd!(bh >> 6 | (src[ip + 1] as usize) << 2);
				ip += 2;
				bh = src[ip] as usize;

				let orig_len = op.len();
				if op.len() < opet {
					mem_move::<32>(op, ipd);
					op.truncate(orig_len + cc);
					continue;
				}
			}
			if op.len() + cc > ope {
				return Err(LZAVError::DstOob);
			}
			op.extend_from_slice(&src[ipd..][..cc]);

			continue;
		}

		// Handle large copy count blocks.
		cc = 16 + mref1;

		if (bh & 32) != 0 { // True, if block type 2 or 3.
			if (bh & 16) == 0 { // True, if block type 2.
				let bv = load!(u32, ip + 1) as usize;
				set_ipd!((bh >> 6) | (bv & 0xFFFF) << 2);
				cc += (bv >> 16) & 0xFF;
				ip += 4;
				bh = bv >> 24;
			} else { // Block type 3.
				let bv = load!(u32, ip + 1) as usize;
				set_ipd_cv!(bv & 0xFFFFFF, bh >> 6, 2);
				cc += bv >> 24;
				ip += 5;
				bh = src[ip] as usize;
			}
		} else { // Block type 1.
			set_ipd!((bh >> 6) | ((src[ip + 1] as usize) << 2));
			cc += src[ip + 2] as usize;
			ip += 3;
			bh = src[ip] as usize;
		}

		if op.len() < opet {
			let orig_len = op.len();
			mem_move::<64>(op, ipd);

			if cc <= 64 {
				op.truncate(orig_len + cc);
				continue;
			}

			ipd += 64;
			cc -= 64;
		}

		if op.len() + cc > ope {
			return Err(LZAVError::DstOob);
		}

		for ii in ipd..ipd+cc {
			op.push(op[ii]);
		}
		continue;
	}

	if op.len() != dstl {
		return Err(LZAVError::DstLen);
	}
	Ok(())
}

fn hd(o: &[u8]) {
	for ii in 0..o.len() {
		if ii != 0 && (ii & 0x1f == 0) {
			println!("");
		}
		print!("{:02x}", o[ii]);
	}
	println!("");
}

fn main() {
	let mut o = Vec::new();
	let src: Vec<u8> = (0..1024).map(|c| c as u8).collect();
	let mut ht = Vec::new();
	lzav_compress(&src, &mut o, &mut ht);
	o.clear();
	lzav_compress_default(&src, &mut o);
	hd(&o);
	let mut dec = Vec::new();
	lzav_decompress(&o, &mut dec, 1024).unwrap();
	assert_eq!(src, dec);
}
