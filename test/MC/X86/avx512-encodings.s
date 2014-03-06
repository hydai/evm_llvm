// RUN: llvm-mc -triple x86_64-unknown-unknown -mcpu=knl --show-encoding %s | FileCheck %s

// CHECK: vaddpd -8192(%rdx), %zmm27, %zmm8
// CHECK:  encoding: [0x62,0x71,0xa5,0x40,0x58,0x42,0x80]
          vaddpd -8192(%rdx), %zmm27, %zmm8

// CHECK: vaddpd -1024(%rdx){1to8}, %zmm27, %zmm8
// CHECK:  encoding: [0x62,0x71,0xa5,0x50,0x58,0x42,0x80]
          vaddpd -1024(%rdx){1to8}, %zmm27, %zmm8

// CHECK: vaddps -8192(%rdx), %zmm13, %zmm18
// CHECK:  encoding: [0x62,0xe1,0x14,0x48,0x58,0x52,0x80]
          vaddps -8192(%rdx), %zmm13, %zmm18

// CHECK: vaddps -512(%rdx){1to16}, %zmm13, %zmm18
// CHECK:  encoding: [0x62,0xe1,0x14,0x58,0x58,0x52,0x80]
          vaddps -512(%rdx){1to16}, %zmm13, %zmm18

// CHECK: vdivpd -8192(%rdx), %zmm6, %zmm18
// CHECK:  encoding: [0x62,0xe1,0xcd,0x48,0x5e,0x52,0x80]
          vdivpd -8192(%rdx), %zmm6, %zmm18

// CHECK: vdivpd -1024(%rdx){1to8}, %zmm6, %zmm18
// CHECK:  encoding: [0x62,0xe1,0xcd,0x58,0x5e,0x52,0x80]
          vdivpd -1024(%rdx){1to8}, %zmm6, %zmm18

// CHECK: vdivps -8192(%rdx), %zmm23, %zmm23
// CHECK:  encoding: [0x62,0xe1,0x44,0x40,0x5e,0x7a,0x80]
          vdivps -8192(%rdx), %zmm23, %zmm23

// CHECK: vdivps -512(%rdx){1to16}, %zmm23, %zmm23
// CHECK:  encoding: [0x62,0xe1,0x44,0x50,0x5e,0x7a,0x80]
          vdivps -512(%rdx){1to16}, %zmm23, %zmm23

// CHECK: vmaxpd -8192(%rdx), %zmm28, %zmm30
// CHECK:  encoding: [0x62,0x61,0x9d,0x40,0x5f,0x72,0x80]
          vmaxpd -8192(%rdx), %zmm28, %zmm30

// CHECK: vmaxpd -1024(%rdx){1to8}, %zmm28, %zmm30
// CHECK:  encoding: [0x62,0x61,0x9d,0x50,0x5f,0x72,0x80]
          vmaxpd -1024(%rdx){1to8}, %zmm28, %zmm30

// CHECK: vmaxps -8192(%rdx), %zmm6, %zmm25
// CHECK:  encoding: [0x62,0x61,0x4c,0x48,0x5f,0x4a,0x80]
          vmaxps -8192(%rdx), %zmm6, %zmm25

// CHECK: vmaxps -512(%rdx){1to16}, %zmm6, %zmm25
// CHECK:  encoding: [0x62,0x61,0x4c,0x58,0x5f,0x4a,0x80]
          vmaxps -512(%rdx){1to16}, %zmm6, %zmm25

// CHECK: vminpd -8192(%rdx), %zmm6, %zmm6
// CHECK:  encoding: [0x62,0xf1,0xcd,0x48,0x5d,0x72,0x80]
          vminpd -8192(%rdx), %zmm6, %zmm6

// CHECK: vminpd -1024(%rdx){1to8}, %zmm6, %zmm6
// CHECK:  encoding: [0x62,0xf1,0xcd,0x58,0x5d,0x72,0x80]
          vminpd -1024(%rdx){1to8}, %zmm6, %zmm6

// CHECK: vminps -8192(%rdx), %zmm3, %zmm3
// CHECK:  encoding: [0x62,0xf1,0x64,0x48,0x5d,0x5a,0x80]
          vminps -8192(%rdx), %zmm3, %zmm3

// CHECK: vminps -512(%rdx){1to16}, %zmm3, %zmm3
// CHECK:  encoding: [0x62,0xf1,0x64,0x58,0x5d,0x5a,0x80]
          vminps -512(%rdx){1to16}, %zmm3, %zmm3

// CHECK: vmulpd -8192(%rdx), %zmm4, %zmm24
// CHECK:  encoding: [0x62,0x61,0xdd,0x48,0x59,0x42,0x80]
          vmulpd -8192(%rdx), %zmm4, %zmm24

// CHECK: vmulpd -1024(%rdx){1to8}, %zmm4, %zmm24
// CHECK:  encoding: [0x62,0x61,0xdd,0x58,0x59,0x42,0x80]
          vmulpd -1024(%rdx){1to8}, %zmm4, %zmm24

// CHECK: vmulps -8192(%rdx), %zmm6, %zmm3
// CHECK:  encoding: [0x62,0xf1,0x4c,0x48,0x59,0x5a,0x80]
          vmulps -8192(%rdx), %zmm6, %zmm3

// CHECK: vmulps -512(%rdx){1to16}, %zmm6, %zmm3
// CHECK:  encoding: [0x62,0xf1,0x4c,0x58,0x59,0x5a,0x80]
          vmulps -512(%rdx){1to16}, %zmm6, %zmm3

// CHECK: vsubpd -8192(%rdx), %zmm12, %zmm9
// CHECK:  encoding: [0x62,0x71,0x9d,0x48,0x5c,0x4a,0x80]
          vsubpd -8192(%rdx), %zmm12, %zmm9

// CHECK: vsubpd -1024(%rdx){1to8}, %zmm12, %zmm9
// CHECK:  encoding: [0x62,0x71,0x9d,0x58,0x5c,0x4a,0x80]
          vsubpd -1024(%rdx){1to8}, %zmm12, %zmm9

// CHECK: vsubps -8192(%rdx), %zmm27, %zmm14
// CHECK:  encoding: [0x62,0x71,0x24,0x40,0x5c,0x72,0x80]
          vsubps -8192(%rdx), %zmm27, %zmm14

// CHECK: vsubps -512(%rdx){1to16}, %zmm27, %zmm14
// CHECK:  encoding: [0x62,0x71,0x24,0x50,0x5c,0x72,0x80]
          vsubps -512(%rdx){1to16}, %zmm27, %zmm14

// CHECK: vinserti32x4
// CHECK: encoding: [0x62,0xa3,0x55,0x48,0x38,0xcd,0x01]
vinserti32x4  $1, %xmm21, %zmm5, %zmm17

// CHECK: vinserti32x4
// CHECK: encoding: [0x62,0xe3,0x1d,0x40,0x38,0x4f,0x10,0x01]
vinserti32x4  $1, 256(%rdi), %zmm28, %zmm17

// CHECK: vextracti32x4
// CHECK: encoding: [0x62,0x33,0x7d,0x48,0x39,0xc9,0x01]
vextracti32x4  $1, %zmm9, %xmm17

// CHECK: vextracti64x4
// CHECK: encoding: [0x62,0x33,0xfd,0x48,0x3b,0xc9,0x01]
vextracti64x4  $1, %zmm9, %ymm17

// CHECK: vextracti64x4
// CHECK: encoding: [0x62,0x73,0xfd,0x48,0x3b,0x4f,0x10,0x01]
vextracti64x4  $1, %zmm9, 512(%rdi)

// CHECK: vpsrad
// CHECK: encoding: [0x62,0xb1,0x35,0x40,0x72,0xe1,0x02]
vpsrad $2, %zmm17, %zmm25

// CHECK: vpsrad
// CHECK: encoding: [0x62,0xf1,0x35,0x40,0x72,0x64,0xb7,0x08,0x02]
vpsrad $2, 512(%rdi, %rsi, 4), %zmm25

// CHECK: vpsrad
// CHECK: encoding: [0x62,0x21,0x1d,0x48,0xe2,0xc9]
vpsrad %xmm17, %zmm12, %zmm25

// CHECK: vpsrad
// CHECK: encoding: [0x62,0x61,0x1d,0x48,0xe2,0x4c,0xb7,0x20]
vpsrad 512(%rdi, %rsi, 4), %zmm12, %zmm25

// CHECK: vpbroadcastd {{.*}} {%k1} {z}
// CHECK: encoding: [0x62,0xf2,0x7d,0xc9,0x58,0xc8]
vpbroadcastd  %xmm0, %zmm1 {%k1} {z}

// CHECK: vmovdqu64 {{.*}} {%k3}
// CHECK: encoding: [0x62,0xf1,0xfe,0x4b,0x6f,0xc8]
vmovdqu64 %zmm0, %zmm1 {%k3}

// CHECK: vmovd
// CHECK: encoding: [0x62,0xe1,0x7d,0x08,0x7e,0x74,0x24,0xeb]
vmovd %xmm22, -84(%rsp)

// CHECK: vextractps
// CHECK: encoding: [0x62,0xe3,0x7d,0x08,0x17,0x61,0x1f,0x02]
vextractps      $2, %xmm20, 124(%rcx)

// CHECK: vaddpd {{.*}}{1to8}
// CHECK: encoding: [0x62,0x61,0xdd,0x50,0x58,0x74,0xf7,0x40]
vaddpd 512(%rdi, %rsi, 8) {1to8}, %zmm20, %zmm30

// CHECK: vaddps {{.*}}{1to16}
// CHECK: encoding: [0x62,0x61,0x5c,0x50,0x58,0xb4,0xf7,0x00,0x02,0x00,0x00]
vaddps 512(%rdi, %rsi, 8) {1to16}, %zmm20, %zmm30
