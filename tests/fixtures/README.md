# Test Fixture COM Programs

Hand-assembled x86 real-mode COM programs for determinism and CPU execution tests.
All programs use ORG 0x100 (standard COM load address).

## counter.com (10 bytes)

Increments byte at address 0x8000 exactly 256 times, then halts.
After execution, `[0x8000]` should be 0x00 (256 wraps a byte to zero).

```asm
0100  B9 00 01     MOV CX, 0x0100
0103  FE 06 00 80  INC BYTE [0x8000]
0107  E2 FA        LOOP 0x0103
0109  F4           HLT
```

## graphics.com (20 bytes)

Switches to VGA Mode 13h (320x200x256), fills first 320 bytes of
video memory (segment 0xA000) with color 0x0F (white), then halts.

```asm
0100  B8 13 00     MOV AX, 0x0013
0103  CD 10        INT 0x10
0105  B8 00 A0     MOV AX, 0xA000
0108  8E C0        MOV ES, AX
010A  31 FF        XOR DI, DI
010C  B9 40 01     MOV CX, 320
010F  B0 0F        MOV AL, 0x0F
0111  F3 AA        REP STOSB
0113  F4           HLT
```

## input.com (8 bytes)

Waits for a keystroke via BIOS INT 16h, stores the ASCII code
at address 0x8000, then halts.

```asm
0100  B4 00        MOV AH, 0x00
0102  CD 16        INT 0x16
0104  A2 00 80     MOV [0x8000], AL
0107  F4           HLT
```
