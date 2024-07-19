	.file	"test8.c"
	.option nopic
	.text
	.align	1
	.globl	test8
	.type	test8, @function
test8:
	addi	sp,sp,-32
	sd	s0,24(sp)
	addi	s0,sp,32
	mv	a5,a0
	sd	a1,-32(s0)
	mv	a4,a2
	sw	a5,-20(s0)
	mv	a5,a4
	sw	a5,-24(s0)
	lw	a5,-20(s0)
	sext.w	a4,a5
	li	a5,15
	bgt	a4,a5,.L2
	lw	a5,-20(s0)
	slli	a5,a5,2
	j	.L3
.L2:
	li	a5,0
.L3:
	ld	a4,-32(s0)
	add	a5,a4,a5
	lw	a4,0(a5)
	li	a5,53248
	addiw	a5,a5,-1282
	mulw	a5,a4,a5
	sw	a5,-24(s0)
	nop
	ld	s0,24(sp)
	addi	sp,sp,32
	jr	ra
	.size	test8, .-test8
	.align	1
	.globl	main
	.type	main, @function
main:
	addi	sp,sp,-96
	sd	ra,88(sp)
	sd	s0,80(sp)
	addi	s0,sp,96
	sw	zero,-20(s0)
	sw	zero,-88(s0)
	li	a5,1
	sw	a5,-84(s0)
	li	a5,2
	sw	a5,-80(s0)
	li	a5,3
	sw	a5,-76(s0)
	li	a5,4
	sw	a5,-72(s0)
	li	a5,5
	sw	a5,-68(s0)
	li	a5,6
	sw	a5,-64(s0)
	li	a5,7
	sw	a5,-60(s0)
	li	a5,8
	sw	a5,-56(s0)
	li	a5,9
	sw	a5,-52(s0)
	li	a5,10
	sw	a5,-48(s0)
	li	a5,11
	sw	a5,-44(s0)
	li	a5,12
	sw	a5,-40(s0)
	li	a5,13
	sw	a5,-36(s0)
	li	a5,14
	sw	a5,-32(s0)
	li	a5,15
	sw	a5,-28(s0)
	li	a5,-559038464
	addiw	a5,a5,-273
	sw	a5,-96(s0)
	lw	a4,-20(s0)
	addi	a5,s0,-88
	mv	a2,a4
	mv	a1,a5
	li	a0,16
	call	test8
	li	a5,0
	mv	a0,a5
	ld	ra,88(sp)
	ld	s0,80(sp)
	addi	sp,sp,96
	jr	ra
	.size	main, .-main
	.ident	"GCC: (GNU) 7.2.0"
