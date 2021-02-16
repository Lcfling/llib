package bytes

import (
	"errors"
)

var (
	ErrInvalidLength   = errors.New("invalid length")
	ErrInvalidPosition = errors.New("invalid position")
	ErrNotEnougth      = errors.New("bytes not enougth")
)

// Buffer .
type Buffer struct {
	total   int
	buffers [][]byte
}

// Len .
func (bb *Buffer) Len() int {
	return bb.total
}

// Push .
func (bb *Buffer) Push(b []byte) {
	if len(b) == 0 {
		return
	}
	bb.buffers = append(bb.buffers, b)
	bb.total += len(b)
}

// Pop .
func (bb *Buffer) Pop(n int) ([]byte, error) {
	if n < 0 {
		return nil, ErrInvalidLength
	}
	if bb.total < n {
		return nil, ErrNotEnougth
	}
	var buf = bb.buffers[0]
	if len(buf) >= n {
		ret := buf[:n]
		bb.buffers[0] = bb.buffers[0][n:]
		if len(bb.buffers[0]) == 0 {
			bb.buffers = bb.buffers[1:]
		}
		return ret, nil
	}

	var ret = make([]byte, n)[0:0]
	for n > 0 {
		if len(buf) >= n {
			ret = append(ret, buf[:n]...)
			bb.buffers[0] = bb.buffers[0][n:]
			if len(bb.buffers[0]) == 0 {
				bb.buffers = bb.buffers[1:]
			}
			return ret, nil
		}
		ret = append(ret, buf...)
		bb.buffers = bb.buffers[1:]
		n -= len(buf)
		buf = bb.buffers[0]
	}
	return ret, nil
}

// Append .
func (bb *Buffer) Append(b []byte) {
	if len(b) == 0 {
		return
	}

	n := len(bb.buffers)

	if n == 0 {
		bb.buffers = append(bb.buffers, b)
		return
	}
	bb.buffers[n-1] = append(bb.buffers[n-1], b...)
	bb.total += len(b)
}

// Head .
func (bb *Buffer) Head(n int) ([]byte, error) {
	if n < 0 {
		return nil, ErrInvalidLength
	}
	if bb.total < n {
		return nil, ErrNotEnougth
	}

	if len(bb.buffers[0]) >= n {
		return bb.buffers[0][:n], nil
	}

	ret := make([]byte, n)

	copied := 0
	for i := 0; n > 0; i++ {
		buf := bb.buffers[i]
		if len(buf) >= n {
			copy(ret[copied:], buf[:n])
			return ret, nil
		} else {
			copy(ret[copied:], buf)
			n -= len(buf)
			copied += len(buf)
		}
	}

	return ret, nil
}

// Sub .
func (bb *Buffer) Sub(from, to int) ([]byte, error) {
	if from < 0 || to < 0 || to < from {
		return nil, ErrInvalidPosition
	}
	if bb.total < to {
		return nil, ErrNotEnougth
	}

	if len(bb.buffers[0]) >= to {
		return bb.buffers[0][from:to], nil
	}

	n := to - from
	ret := make([]byte, n)
	copied := 0
	for i := 0; n > 0; i++ {
		buf := bb.buffers[i]
		if len(buf) >= from+n {
			copy(ret[copied:], buf[from:from+n])
			return ret, nil
		} else {
			if len(buf) > from {
				if from > 0 {
					buf = buf[from:]
					from = 0
				}
				copy(ret[copied:], buf)
				copied += len(buf)
				n -= len(buf)
			} else {
				from -= len(buf)
			}
		}
	}

	return ret, nil
}

// Write .
func (bb *Buffer) Write(b []byte) {
	bb.Push(b)
}

// Read .
func (bb *Buffer) Read(n int) ([]byte, error) {
	return bb.Pop(n)
}

// ReadAll .
func (bb *Buffer) ReadAll() ([]byte, error) {
	if len(bb.buffers) == 0 {
		return nil, nil
	}

	buf := bb.buffers[0]
	for i := 1; i < len(bb.buffers); i++ {
		buf = append(buf, bb.buffers[i]...)
	}
	bb.buffers = nil

	return buf, nil
}

// Reset .
func (bb *Buffer) Reset() {
	bb.buffers = nil
	bb.total = 0
}

// NewBuffer .
func NewBuffer() *Buffer {
	return &Buffer{}
}
