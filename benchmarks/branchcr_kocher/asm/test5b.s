	.file	"test5b.c"
	.option nopic
	.text
	.align	1
	.globl	test5b
	.type	test5b, @function
test5b:
	addi	sp,sp,-48
	sd	s0,40(sp)
	addi	s0,sp,48
	mv	a5,a0
	sd	a1,-48(s0)
	mv	a4,a2
	sw	a5,-36(s0)
	mv	a5,a4
	sw	a5,-40(s0)
	lw	a5,-36(s0)
	sext.w	a4,a5
	li	a5,15
	bgt	a4,a5,.L5
	lw	a5,-36(s0)
	addiw	a5,a5,-1
	sw	a5,-20(s0)
	j	.L3
.L4:
	lw	a5,-20(s0)
	slli	a5,a5,2
	ld	a4,-48(s0)
	add	a5,a4,a5
	lw	a4,0(a5)
	li	a5,53248
	addiw	a5,a5,-1282
	mulw	a5,a4,a5
	sw	a5,-40(s0)
	lw	a5,-20(s0)
	addiw	a5,a5,-1
	sw	a5,-20(s0)
.L3:
	lw	a5,-20(s0)
	sext.w	a5,a5
	bgez	a5,.L4
.L5:
	nop
	ld	s0,40(sp)
	addi	sp,sp,48
	jr	ra
	.size	test5b, .-test5b
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
	li	a0,17
	call	test5b
	li	a5,0
	mv	a0,a5
	ld	ra,88(sp)
	ld	s0,80(sp)
	addi	sp,sp,96
	jr	ra
	.size	main, .-main
	.ident	"GCC: (GNU) 7.2.0"
