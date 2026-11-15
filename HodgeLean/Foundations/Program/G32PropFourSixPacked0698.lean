import HodgeLean.Foundations.Program.HurwitzPrymRexG32Core

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0001 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
23
else
0)
else
(if i.val < 515 then
0
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
23)
else
(if i.val < 519 then
23
else
6)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
35
else
0)
else
(if i.val < 523 then
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
0)
else
(if i.val < 527 then
0
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
14
else
0)
else
(if i.val < 531 then
0
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
14
else
0)
else
(if i.val < 535 then
0
else
11)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
0
else
0)
else
(if i.val < 539 then
0
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
0
else
0)
else
(if i.val < 543 then
0
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
0
else
0)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
0
else
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
28)
else
(if i.val < 555 then
0
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
0
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
0)
else
(if i.val < 563 then
0
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
0
else
0)
else
(if i.val < 567 then
27
else
27)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
0
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
0)
else
(if i.val < 575 then
0
else
0))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
0)
else
(if i.val < 579 then
0
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
0)
else
(if i.val < 583 then
0
else
8)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
27)
else
(if i.val < 587 then
0
else
0))
else
(if i.val < 590 then
(if i.val < 589 then
0
else
0)
else
(if i.val < 591 then
0
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
0)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
0)
else
(if i.val < 599 then
0
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
27
else
0)
else
(if i.val < 603 then
0
else
27))
else
(if i.val < 606 then
(if i.val < 605 then
9
else
0)
else
(if i.val < 607 then
10
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
0)
else
(if i.val < 611 then
0
else
0))
else
(if i.val < 614 then
(if i.val < 613 then
0
else
0)
else
(if i.val < 615 then
0
else
0)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
0
else
0)
else
(if i.val < 619 then
8
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
0
else
0)
else
(if i.val < 623 then
0
else
0))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
0
else
0)
else
(if i.val < 627 then
8
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
12
else
0)
else
(if i.val < 631 then
21
else
24)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
0)
else
(if i.val < 635 then
23
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
0)
else
(if i.val < 639 then
0
else
0)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
16
else
0)
else
(if i.val < 643 then
28
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
0
else
0)
else
(if i.val < 647 then
0
else
0)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
0)
else
(if i.val < 651 then
0
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
0)
else
(if i.val < 655 then
0
else
0))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
0
else
0)
else
(if i.val < 659 then
18
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
0
else
0)
else
(if i.val < 663 then
0
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
0)
else
(if i.val < 667 then
31
else
8))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
0)
else
(if i.val < 671 then
0
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
else
0)
else
(if i.val < 675 then
33
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
8
else
0)
else
(if i.val < 679 then
0
else
0)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
8
else
0)
else
(if i.val < 683 then
0
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
33)
else
(if i.val < 687 then
10
else
9))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
0
else
0)
else
(if i.val < 691 then
0
else
0))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
0)
else
(if i.val < 695 then
0
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
0
else
0)
else
(if i.val < 699 then
0
else
12))
else
(if i.val < 702 then
(if i.val < 701 then
0
else
0)
else
(if i.val < 703 then
0
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
0
else
0)
else
(if i.val < 707 then
0
else
8))
else
(if i.val < 710 then
(if i.val < 709 then
8
else
0)
else
(if i.val < 711 then
0
else
24)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
29
else
0)
else
(if i.val < 715 then
0
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
23
else
6)
else
(if i.val < 719 then
0
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
0
else
0)
else
(if i.val < 723 then
21
else
8))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
0)
else
(if i.val < 727 then
35
else
0)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
25
else
0)
else
(if i.val < 731 then
0
else
23))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
25)
else
(if i.val < 735 then
23
else
23)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
6
else
8)
else
(if i.val < 739 then
22
else
8))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
0)
else
(if i.val < 743 then
0
else
8)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
0)
else
(if i.val < 747 then
0
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
0)
else
(if i.val < 751 then
0
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
14
else
14)
else
(if i.val < 755 then
0
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
0)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
14
else
14)
else
(if i.val < 763 then
11
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
11
else
0)
else
(if i.val < 767 then
14
else
0))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
0
else
11)
else
(if i.val < 771 then
0
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
18
else
0)
else
(if i.val < 775 then
0
else
14)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
0)
else
(if i.val < 779 then
0
else
0))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
else
(if i.val < 783 then
0
else
0))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
0)
else
(if i.val < 787 then
0
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
0)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
0)
else
(if i.val < 795 then
0
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
0)
else
(if i.val < 799 then
0
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
0)
else
(if i.val < 803 then
0
else
0))
else
(if i.val < 806 then
(if i.val < 805 then
0
else
0)
else
(if i.val < 807 then
0
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
0
else
10)
else
(if i.val < 811 then
0
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
14)
else
(if i.val < 815 then
0
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
27)
else
(if i.val < 819 then
0
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
0)
else
(if i.val < 823 then
12
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
0
else
0)
else
(if i.val < 827 then
0
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
16)
else
(if i.val < 831 then
31
else
14))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
0
else
11)
else
(if i.val < 835 then
14
else
0))
else
(if i.val < 838 then
(if i.val < 837 then
0
else
0)
else
(if i.val < 839 then
0
else
24)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
0
else
0)
else
(if i.val < 843 then
10
else
27))
else
(if i.val < 846 then
(if i.val < 845 then
24
else
10)
else
(if i.val < 847 then
0
else
0))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
0
else
0)
else
(if i.val < 851 then
0
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
0)
else
(if i.val < 855 then
0
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
0)
else
(if i.val < 859 then
0
else
8))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
12)
else
(if i.val < 863 then
0
else
25)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
0)
else
(if i.val < 867 then
0
else
0))
else
(if i.val < 870 then
(if i.val < 869 then
0
else
0)
else
(if i.val < 871 then
0
else
29)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
0
else
0)
else
(if i.val < 875 then
0
else
22))
else
(if i.val < 878 then
(if i.val < 877 then
0
else
25)
else
(if i.val < 879 then
0
else
0))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
0)
else
(if i.val < 883 then
0
else
0))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
0)
else
(if i.val < 887 then
0
else
0)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
0)
else
(if i.val < 891 then
0
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
0
else
0)
else
(if i.val < 895 then
0
else
18)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
18
else
31)
else
(if i.val < 899 then
0
else
6))
else
(if i.val < 902 then
(if i.val < 901 then
27
else
0)
else
(if i.val < 903 then
0
else
0)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
0)
else
(if i.val < 907 then
0
else
8))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
0)
else
(if i.val < 911 then
0
else
0))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
0
else
23)
else
(if i.val < 915 then
0
else
0))
else
(if i.val < 918 then
(if i.val < 917 then
32
else
0)
else
(if i.val < 919 then
0
else
0)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
18
else
0)
else
(if i.val < 923 then
0
else
0))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
11)
else
(if i.val < 927 then
0
else
0)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
0
else
8)
else
(if i.val < 931 then
0
else
0))
else
(if i.val < 934 then
(if i.val < 933 then
0
else
0)
else
(if i.val < 935 then
0
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
0
else
0)
else
(if i.val < 939 then
0
else
27))
else
(if i.val < 942 then
(if i.val < 941 then
0
else
0)
else
(if i.val < 943 then
0
else
8))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
0
else
0)
else
(if i.val < 947 then
0
else
0))
else
(if i.val < 950 then
(if i.val < 949 then
23
else
23)
else
(if i.val < 951 then
5
else
0)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
0)
else
(if i.val < 955 then
0
else
14))
else
(if i.val < 958 then
(if i.val < 957 then
0
else
28)
else
(if i.val < 959 then
11
else
14))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
11
else
11)
else
(if i.val < 963 then
0
else
0))
else
(if i.val < 966 then
(if i.val < 965 then
20
else
11)
else
(if i.val < 967 then
0
else
0)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
0
else
0)
else
(if i.val < 971 then
0
else
0))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
0)
else
(if i.val < 975 then
28
else
0))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
0)
else
(if i.val < 979 then
0
else
0))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
0)
else
(if i.val < 983 then
0
else
11)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
11
else
11)
else
(if i.val < 987 then
11
else
27))
else
(if i.val < 990 then
(if i.val < 989 then
27
else
0)
else
(if i.val < 991 then
0
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
32
else
0)
else
(if i.val < 995 then
0
else
0))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
0)
else
(if i.val < 999 then
0
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
29
else
0)
else
(if i.val < 1003 then
0
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
8
else
0)
else
(if i.val < 1007 then
0
else
6))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
0)
else
(if i.val < 1011 then
0
else
0))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
0)
else
(if i.val < 1015 then
0
else
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
0
else
27))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
0)
else
(if i.val < 1023 then
27
else
9)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0002 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
10
else
23)
else
(if i.val < 1027 then
0
else
0))
else
(if i.val < 1030 then
(if i.val < 1029 then
0
else
0)
else
(if i.val < 1031 then
0
else
0)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
0
else
0)
else
(if i.val < 1035 then
0
else
0))
else
(if i.val < 1038 then
(if i.val < 1037 then
8
else
27)
else
(if i.val < 1039 then
0
else
0))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
0
else
0)
else
(if i.val < 1043 then
0
else
23))
else
(if i.val < 1046 then
(if i.val < 1045 then
32
else
0)
else
(if i.val < 1047 then
12
else
0)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
24
else
23)
else
(if i.val < 1051 then
0
else
0))
else
(if i.val < 1054 then
(if i.val < 1053 then
0
else
0)
else
(if i.val < 1055 then
16
else
0)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
28
else
0)
else
(if i.val < 1059 then
0
else
0))
else
(if i.val < 1062 then
(if i.val < 1061 then
0
else
0)
else
(if i.val < 1063 then
0
else
0)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
33
else
0)
else
(if i.val < 1067 then
28
else
0))
else
(if i.val < 1070 then
(if i.val < 1069 then
0
else
0)
else
(if i.val < 1071 then
18
else
0))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
0
else
0)
else
(if i.val < 1075 then
0
else
0))
else
(if i.val < 1078 then
(if i.val < 1077 then
27
else
31)
else
(if i.val < 1079 then
35
else
0)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
0
else
0)
else
(if i.val < 1083 then
0
else
22))
else
(if i.val < 1086 then
(if i.val < 1085 then
0
else
33)
else
(if i.val < 1087 then
8
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
0
else
23)
else
(if i.val < 1091 then
8
else
0))
else
(if i.val < 1094 then
(if i.val < 1093 then
0
else
0)
else
(if i.val < 1095 then
10
else
6)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
0
else
0)
else
(if i.val < 1099 then
0
else
0))
else
(if i.val < 1102 then
(if i.val < 1101 then
0
else
0)
else
(if i.val < 1103 then
0
else
0))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
0
else
0)
else
(if i.val < 1107 then
0
else
12))
else
(if i.val < 1110 then
(if i.val < 1109 then
0
else
0)
else
(if i.val < 1111 then
0
else
0)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
0
else
0)
else
(if i.val < 1115 then
27
else
8))
else
(if i.val < 1118 then
(if i.val < 1117 then
8
else
0)
else
(if i.val < 1119 then
0
else
24)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
29
else
0)
else
(if i.val < 1123 then
0
else
23))
else
(if i.val < 1126 then
(if i.val < 1125 then
0
else
0)
else
(if i.val < 1127 then
0
else
0)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
21
else
8)
else
(if i.val < 1131 then
0
else
0))
else
(if i.val < 1134 then
(if i.val < 1133 then
23
else
23)
else
(if i.val < 1135 then
0
else
23))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
23
else
6)
else
(if i.val < 1139 then
8
else
8))
else
(if i.val < 1142 then
(if i.val < 1141 then
26
else
0)
else
(if i.val < 1143 then
8
else
0)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
0
else
0)
else
(if i.val < 1147 then
35
else
0))
else
(if i.val < 1150 then
(if i.val < 1149 then
18
else
28)
else
(if i.val < 1151 then
29
else
13)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
14
else
28)
else
(if i.val < 1155 then
0
else
0))
else
(if i.val < 1158 then
(if i.val < 1157 then
0
else
0)
else
(if i.val < 1159 then
14
else
14)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
0
else
11)
else
(if i.val < 1163 then
14
else
0))
else
(if i.val < 1166 then
(if i.val < 1165 then
0
else
11)
else
(if i.val < 1167 then
0
else
0))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
0
else
28)
else
(if i.val < 1171 then
0
else
0))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
0)
else
(if i.val < 1175 then
0
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
0)
else
(if i.val < 1179 then
0
else
0))
else
(if i.val < 1182 then
(if i.val < 1181 then
0
else
0)
else
(if i.val < 1183 then
0
else
0)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
0
else
0)
else
(if i.val < 1187 then
0
else
0))
else
(if i.val < 1190 then
(if i.val < 1189 then
0
else
0)
else
(if i.val < 1191 then
0
else
0)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
0
else
0)
else
(if i.val < 1195 then
0
else
0))
else
(if i.val < 1198 then
(if i.val < 1197 then
0
else
10)
else
(if i.val < 1199 then
0
else
28))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
0
else
14)
else
(if i.val < 1203 then
0
else
0))
else
(if i.val < 1206 then
(if i.val < 1205 then
0
else
27)
else
(if i.val < 1207 then
0
else
0)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
0
else
0)
else
(if i.val < 1211 then
12
else
0))
else
(if i.val < 1214 then
(if i.val < 1213 then
0
else
0)
else
(if i.val < 1215 then
0
else
28))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
16
else
31)
else
(if i.val < 1219 then
14
else
0))
else
(if i.val < 1222 then
(if i.val < 1221 then
11
else
14)
else
(if i.val < 1223 then
0
else
28)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
27
else
24)
else
(if i.val < 1227 then
0
else
0))
else
(if i.val < 1230 then
(if i.val < 1229 then
10
else
27)
else
(if i.val < 1231 then
24
else
10))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
26
else
18)
else
(if i.val < 1235 then
0
else
0))
else
(if i.val < 1238 then
(if i.val < 1237 then
28
else
0)
else
(if i.val < 1239 then
23
else
21)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
0
else
0)
else
(if i.val < 1243 then
0
else
0))
else
(if i.val < 1246 then
(if i.val < 1245 then
8
else
0)
else
(if i.val < 1247 then
12
else
0)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
25
else
0)
else
(if i.val < 1251 then
27
else
27))
else
(if i.val < 1254 then
(if i.val < 1253 then
0
else
0)
else
(if i.val < 1255 then
0
else
0)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
29
else
0)
else
(if i.val < 1259 then
0
else
0))
else
(if i.val < 1262 then
(if i.val < 1261 then
22
else
6)
else
(if i.val < 1263 then
25
else
0))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
0
else
0)
else
(if i.val < 1267 then
0
else
0))
else
(if i.val < 1270 then
(if i.val < 1269 then
0
else
0)
else
(if i.val < 1271 then
0
else
0)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
29
else
0)
else
(if i.val < 1275 then
0
else
0))
else
(if i.val < 1278 then
(if i.val < 1277 then
0
else
0)
else
(if i.val < 1279 then
18
else
18))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
31
else
27)
else
(if i.val < 1283 then
0
else
0))
else
(if i.val < 1286 then
(if i.val < 1285 then
0
else
0)
else
(if i.val < 1287 then
0
else
6)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
0
else
5)
else
(if i.val < 1291 then
20
else
12))
else
(if i.val < 1294 then
(if i.val < 1293 then
0
else
27)
else
(if i.val < 1295 then
0
else
0))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
9
else
8)
else
(if i.val < 1299 then
27
else
0))
else
(if i.val < 1302 then
(if i.val < 1301 then
0
else
12)
else
(if i.val < 1303 then
29
else
0)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
8
else
0)
else
(if i.val < 1307 then
8
else
0))
else
(if i.val < 1310 then
(if i.val < 1309 then
0
else
0)
else
(if i.val < 1311 then
0
else
23)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
0
else
0)
else
(if i.val < 1315 then
0
else
0))
else
(if i.val < 1318 then
(if i.val < 1317 then
8
else
0)
else
(if i.val < 1319 then
0
else
10)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
0
else
29)
else
(if i.val < 1323 then
0
else
0))
else
(if i.val < 1326 then
(if i.val < 1325 then
0
else
12)
else
(if i.val < 1327 then
0
else
0))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
0
else
0)
else
(if i.val < 1331 then
0
else
0))
else
(if i.val < 1334 then
(if i.val < 1333 then
0
else
8)
else
(if i.val < 1335 then
0
else
12)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
0
else
21)
else
(if i.val < 1339 then
29
else
25))
else
(if i.val < 1342 then
(if i.val < 1341 then
24
else
8)
else
(if i.val < 1343 then
0
else
23))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
8
else
8)
else
(if i.val < 1347 then
0
else
16))
else
(if i.val < 1350 then
(if i.val < 1349 then
8
else
28)
else
(if i.val < 1351 then
0
else
8)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
21
else
8)
else
(if i.val < 1355 then
0
else
20))
else
(if i.val < 1358 then
(if i.val < 1357 then
0
else
0)
else
(if i.val < 1359 then
0
else
0))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
23
else
0)
else
(if i.val < 1363 then
6
else
22))
else
(if i.val < 1366 then
(if i.val < 1365 then
19
else
0)
else
(if i.val < 1367 then
24
else
0)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
0
else
31)
else
(if i.val < 1371 then
2
else
0))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
14)
else
(if i.val < 1375 then
18
else
0)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
0
else
0)
else
(if i.val < 1379 then
9
else
8))
else
(if i.val < 1382 then
(if i.val < 1381 then
0
else
18)
else
(if i.val < 1383 then
0
else
0)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
0
else
14)
else
(if i.val < 1387 then
0
else
0))
else
(if i.val < 1390 then
(if i.val < 1389 then
0
else
0)
else
(if i.val < 1391 then
0
else
18))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
21
else
0)
else
(if i.val < 1395 then
0
else
17))
else
(if i.val < 1398 then
(if i.val < 1397 then
0
else
0)
else
(if i.val < 1399 then
0
else
31)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
0
else
0)
else
(if i.val < 1403 then
0
else
16))
else
(if i.val < 1406 then
(if i.val < 1405 then
16
else
0)
else
(if i.val < 1407 then
0
else
32)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
18
else
0)
else
(if i.val < 1411 then
0
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
0
else
0)
else
(if i.val < 1415 then
0
else
0)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
0
else
0)
else
(if i.val < 1419 then
11
else
0))
else
(if i.val < 1422 then
(if i.val < 1421 then
24
else
18)
else
(if i.val < 1423 then
18
else
0))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
0
else
25)
else
(if i.val < 1427 then
0
else
21))
else
(if i.val < 1430 then
(if i.val < 1429 then
0
else
17)
else
(if i.val < 1431 then
0
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
24
else
8)
else
(if i.val < 1435 then
21
else
35))
else
(if i.val < 1438 then
(if i.val < 1437 then
25
else
0)
else
(if i.val < 1439 then
25
else
22)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
22
else
24)
else
(if i.val < 1443 then
0
else
8))
else
(if i.val < 1446 then
(if i.val < 1445 then
0
else
0)
else
(if i.val < 1447 then
0
else
17)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
19
else
0)
else
(if i.val < 1451 then
10
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
0
else
29)
else
(if i.val < 1455 then
0
else
0))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
0
else
0)
else
(if i.val < 1459 then
0
else
0))
else
(if i.val < 1462 then
(if i.val < 1461 then
0
else
0)
else
(if i.val < 1463 then
0
else
0)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
0
else
0)
else
(if i.val < 1467 then
0
else
27))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
0)
else
(if i.val < 1471 then
0
else
0))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
10
else
0)
else
(if i.val < 1475 then
32
else
10))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
0)
else
(if i.val < 1479 then
0
else
0)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
0
else
0)
else
(if i.val < 1483 then
22
else
0))
else
(if i.val < 1486 then
(if i.val < 1485 then
12
else
20)
else
(if i.val < 1487 then
29
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
22
else
22)
else
(if i.val < 1491 then
6
else
8))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
0)
else
(if i.val < 1495 then
0
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
21
else
8)
else
(if i.val < 1499 then
0
else
0))
else
(if i.val < 1502 then
(if i.val < 1501 then
35
else
0)
else
(if i.val < 1503 then
23
else
0)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
25
else
35)
else
(if i.val < 1507 then
6
else
22))
else
(if i.val < 1510 then
(if i.val < 1509 then
8
else
0)
else
(if i.val < 1511 then
0
else
35)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
0)
else
(if i.val < 1515 then
21
else
8))
else
(if i.val < 1518 then
(if i.val < 1517 then
0
else
0)
else
(if i.val < 1519 then
24
else
0))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
25
else
20)
else
(if i.val < 1523 then
23
else
24))
else
(if i.val < 1526 then
(if i.val < 1525 then
24
else
8)
else
(if i.val < 1527 then
8
else
0)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
0
else
23)
else
(if i.val < 1531 then
0
else
25))
else
(if i.val < 1534 then
(if i.val < 1533 then
23
else
23)
else
(if i.val < 1535 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0003 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
0
else
23)
else
(if i.val < 1539 then
22
else
22))
else
(if i.val < 1542 then
(if i.val < 1541 then
24
else
23)
else
(if i.val < 1543 then
23
else
6)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
23
else
8)
else
(if i.val < 1547 then
0
else
8))
else
(if i.val < 1550 then
(if i.val < 1549 then
21
else
0)
else
(if i.val < 1551 then
0
else
8))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
0
else
0)
else
(if i.val < 1555 then
0
else
28))
else
(if i.val < 1558 then
(if i.val < 1557 then
8
else
0)
else
(if i.val < 1559 then
0
else
18)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
16)
else
(if i.val < 1563 then
0
else
0))
else
(if i.val < 1566 then
(if i.val < 1565 then
25
else
25)
else
(if i.val < 1567 then
11
else
0)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
16
else
0)
else
(if i.val < 1571 then
0
else
28))
else
(if i.val < 1574 then
(if i.val < 1573 then
0
else
13)
else
(if i.val < 1575 then
0
else
27)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
10
else
10)
else
(if i.val < 1579 then
27
else
0))
else
(if i.val < 1582 then
(if i.val < 1581 then
14
else
14)
else
(if i.val < 1583 then
11
else
14))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
14
else
0)
else
(if i.val < 1587 then
14
else
11))
else
(if i.val < 1590 then
(if i.val < 1589 then
0
else
14)
else
(if i.val < 1591 then
0
else
18)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
12
else
14)
else
(if i.val < 1595 then
18
else
14))
else
(if i.val < 1598 then
(if i.val < 1597 then
0
else
32)
else
(if i.val < 1599 then
0
else
11))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
11
else
0)
else
(if i.val < 1603 then
18
else
0))
else
(if i.val < 1606 then
(if i.val < 1605 then
14
else
32)
else
(if i.val < 1607 then
33
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
18
else
14)
else
(if i.val < 1611 then
0
else
0))
else
(if i.val < 1614 then
(if i.val < 1613 then
18
else
0)
else
(if i.val < 1615 then
0
else
0))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
0
else
0)
else
(if i.val < 1619 then
0
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
0
else
0)
else
(if i.val < 1623 then
0
else
0)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
0
else
0)
else
(if i.val < 1627 then
0
else
0))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
0)
else
(if i.val < 1631 then
0
else
0)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
0
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
0
else
0)
else
(if i.val < 1639 then
0
else
0)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
0
else
0)
else
(if i.val < 1643 then
0
else
0))
else
(if i.val < 1646 then
(if i.val < 1645 then
0
else
0)
else
(if i.val < 1647 then
0
else
0))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
0
else
0)
else
(if i.val < 1651 then
11
else
25))
else
(if i.val < 1654 then
(if i.val < 1653 then
0
else
0)
else
(if i.val < 1655 then
0
else
0)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
0
else
0)
else
(if i.val < 1659 then
12
else
14))
else
(if i.val < 1662 then
(if i.val < 1661 then
28
else
0)
else
(if i.val < 1663 then
0
else
14)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
0
else
1)
else
(if i.val < 1667 then
14
else
14))
else
(if i.val < 1670 then
(if i.val < 1669 then
0
else
27)
else
(if i.val < 1671 then
0
else
10)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
16
else
0)
else
(if i.val < 1675 then
0
else
33))
else
(if i.val < 1678 then
(if i.val < 1677 then
0
else
25)
else
(if i.val < 1679 then
21
else
29))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
10
else
0)
else
(if i.val < 1683 then
0
else
18))
else
(if i.val < 1686 then
(if i.val < 1685 then
0
else
0)
else
(if i.val < 1687 then
0
else
25)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
27
else
10)
else
(if i.val < 1691 then
11
else
0))
else
(if i.val < 1694 then
(if i.val < 1693 then
10
else
28)
else
(if i.val < 1695 then
11
else
27)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
31
else
14)
else
(if i.val < 1699 then
14
else
11))
else
(if i.val < 1702 then
(if i.val < 1701 then
0
else
0)
else
(if i.val < 1703 then
0
else
0)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
9
else
0)
else
(if i.val < 1707 then
0
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
0
else
5)
else
(if i.val < 1711 then
20
else
12))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
0
else
10)
else
(if i.val < 1715 then
24
else
25))
else
(if i.val < 1718 then
(if i.val < 1717 then
0
else
0)
else
(if i.val < 1719 then
0
else
0)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
12)
else
(if i.val < 1723 then
2
else
0))
else
(if i.val < 1726 then
(if i.val < 1725 then
0
else
0)
else
(if i.val < 1727 then
0
else
31))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
0
else
25)
else
(if i.val < 1731 then
8
else
17))
else
(if i.val < 1734 then
(if i.val < 1733 then
0
else
0)
else
(if i.val < 1735 then
0
else
19)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
0
else
0)
else
(if i.val < 1739 then
17
else
35))
else
(if i.val < 1742 then
(if i.val < 1741 then
0
else
0)
else
(if i.val < 1743 then
0
else
29))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
0
else
29)
else
(if i.val < 1747 then
0
else
0))
else
(if i.val < 1750 then
(if i.val < 1749 then
8
else
12)
else
(if i.val < 1751 then
0
else
0)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
26
else
0)
else
(if i.val < 1755 then
0
else
10))
else
(if i.val < 1758 then
(if i.val < 1757 then
25
else
0)
else
(if i.val < 1759 then
0
else
21)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
22
else
5)
else
(if i.val < 1763 then
0
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
6
else
8)
else
(if i.val < 1767 then
29
else
0)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
33
else
0)
else
(if i.val < 1771 then
12
else
0))
else
(if i.val < 1774 then
(if i.val < 1773 then
0
else
6)
else
(if i.val < 1775 then
0
else
10))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
0
else
0)
else
(if i.val < 1779 then
9
else
18))
else
(if i.val < 1782 then
(if i.val < 1781 then
0
else
0)
else
(if i.val < 1783 then
0
else
16)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
18
else
0)
else
(if i.val < 1787 then
0
else
0))
else
(if i.val < 1790 then
(if i.val < 1789 then
1
else
0)
else
(if i.val < 1791 then
31
else
0))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
0
else
25)
else
(if i.val < 1795 then
18
else
18))
else
(if i.val < 1798 then
(if i.val < 1797 then
0
else
21)
else
(if i.val < 1799 then
0
else
0)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
21
else
32)
else
(if i.val < 1803 then
18
else
35))
else
(if i.val < 1806 then
(if i.val < 1805 then
0
else
6)
else
(if i.val < 1807 then
0
else
27))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
27
else
10)
else
(if i.val < 1811 then
10
else
23))
else
(if i.val < 1814 then
(if i.val < 1813 then
0
else
27)
else
(if i.val < 1815 then
0
else
0)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
0
else
0)
else
(if i.val < 1819 then
0
else
8))
else
(if i.val < 1822 then
(if i.val < 1821 then
27
else
0)
else
(if i.val < 1823 then
35
else
0)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
0
else
0)
else
(if i.val < 1827 then
23
else
8))
else
(if i.val < 1830 then
(if i.val < 1829 then
22
else
12)
else
(if i.val < 1831 then
32
else
23)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
0
else
0)
else
(if i.val < 1835 then
0
else
0))
else
(if i.val < 1838 then
(if i.val < 1837 then
0
else
0)
else
(if i.val < 1839 then
0
else
18))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
18
else
33)
else
(if i.val < 1843 then
0
else
28))
else
(if i.val < 1846 then
(if i.val < 1845 then
0
else
18)
else
(if i.val < 1847 then
18
else
0)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
0
else
11)
else
(if i.val < 1851 then
27
else
31))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
0
else
8))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
0
else
22)
else
(if i.val < 1859 then
23
else
0))
else
(if i.val < 1862 then
(if i.val < 1861 then
0
else
10)
else
(if i.val < 1863 then
6
else
0)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
11
else
0)
else
(if i.val < 1867 then
0
else
0))
else
(if i.val < 1870 then
(if i.val < 1869 then
0
else
0)
else
(if i.val < 1871 then
0
else
10))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
0
else
11)
else
(if i.val < 1875 then
12
else
34))
else
(if i.val < 1878 then
(if i.val < 1877 then
35
else
0)
else
(if i.val < 1879 then
27
else
8)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
8
else
35)
else
(if i.val < 1883 then
29
else
0))
else
(if i.val < 1886 then
(if i.val < 1885 then
0
else
23)
else
(if i.val < 1887 then
5
else
27)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
0
else
8)
else
(if i.val < 1891 then
8
else
0))
else
(if i.val < 1894 then
(if i.val < 1893 then
0
else
23)
else
(if i.val < 1895 then
0
else
23)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
23
else
35)
else
(if i.val < 1899 then
26
else
0))
else
(if i.val < 1902 then
(if i.val < 1901 then
21
else
0)
else
(if i.val < 1903 then
0
else
0))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
0
else
29)
else
(if i.val < 1907 then
14
else
28))
else
(if i.val < 1910 then
(if i.val < 1909 then
0
else
11)
else
(if i.val < 1911 then
11
else
11)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
11
else
11)
else
(if i.val < 1915 then
18
else
13))
else
(if i.val < 1918 then
(if i.val < 1917 then
0
else
11)
else
(if i.val < 1919 then
11
else
11)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
0
else
0)
else
(if i.val < 1923 then
0
else
0))
else
(if i.val < 1926 then
(if i.val < 1925 then
0
else
0)
else
(if i.val < 1927 then
0
else
0)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
0)
else
(if i.val < 1931 then
0
else
0))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
0)
else
(if i.val < 1935 then
10
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
0
else
14)
else
(if i.val < 1939 then
0
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
11
else
27)
else
(if i.val < 1943 then
0
else
27)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
0
else
12)
else
(if i.val < 1947 then
0
else
0))
else
(if i.val < 1950 then
(if i.val < 1949 then
11
else
28)
else
(if i.val < 1951 then
11
else
11)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
28
else
11)
else
(if i.val < 1955 then
11
else
0))
else
(if i.val < 1958 then
(if i.val < 1957 then
28
else
29)
else
(if i.val < 1959 then
24
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
10)
else
(if i.val < 1963 then
24
else
26))
else
(if i.val < 1966 then
(if i.val < 1965 then
18
else
22)
else
(if i.val < 1967 then
23
else
21))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
0
else
33)
else
(if i.val < 1971 then
0
else
0))
else
(if i.val < 1974 then
(if i.val < 1973 then
8
else
0)
else
(if i.val < 1975 then
12
else
32)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
27
else
27)
else
(if i.val < 1979 then
0
else
0))
else
(if i.val < 1982 then
(if i.val < 1981 then
29
else
29)
else
(if i.val < 1983 then
29
else
5))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
10
else
0)
else
(if i.val < 1987 then
22
else
6))
else
(if i.val < 1990 then
(if i.val < 1989 then
25
else
0)
else
(if i.val < 1991 then
10
else
10)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
0
else
0)
else
(if i.val < 1995 then
0
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
32
else
0)
else
(if i.val < 1999 then
0
else
31))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
0
else
0)
else
(if i.val < 2003 then
0
else
0))
else
(if i.val < 2006 then
(if i.val < 2005 then
0
else
6)
else
(if i.val < 2007 then
6
else
5)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
20
else
12)
else
(if i.val < 2011 then
0
else
27))
else
(if i.val < 2014 then
(if i.val < 2013 then
0
else
0)
else
(if i.val < 2015 then
8
else
12)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
27
else
0)
else
(if i.val < 2019 then
12
else
29))
else
(if i.val < 2022 then
(if i.val < 2021 then
0
else
10)
else
(if i.val < 2023 then
32
else
23)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
0
else
0)
else
(if i.val < 2027 then
8
else
0))
else
(if i.val < 2030 then
(if i.val < 2029 then
0
else
10)
else
(if i.val < 2031 then
0
else
29))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
0
else
23)
else
(if i.val < 2035 then
0
else
12))
else
(if i.val < 2038 then
(if i.val < 2037 then
0
else
0)
else
(if i.val < 2039 then
0
else
0)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
0
else
0)
else
(if i.val < 2043 then
23
else
22))
else
(if i.val < 2046 then
(if i.val < 2045 then
22
else
12)
else
(if i.val < 2047 then
0
else
29)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0004 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
25
else
24)
else
(if i.val < 2051 then
23
else
23))
else
(if i.val < 2054 then
(if i.val < 2053 then
6
else
0)
else
(if i.val < 2055 then
11
else
33)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
31
else
0)
else
(if i.val < 2059 then
23
else
8))
else
(if i.val < 2062 then
(if i.val < 2061 then
32
else
6)
else
(if i.val < 2063 then
0
else
0))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
31
else
2)
else
(if i.val < 2067 then
0
else
0))
else
(if i.val < 2070 then
(if i.val < 2069 then
14
else
0)
else
(if i.val < 2071 then
0
else
0)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
8
else
0)
else
(if i.val < 2075 then
0
else
27))
else
(if i.val < 2078 then
(if i.val < 2077 then
0
else
0)
else
(if i.val < 2079 then
0
else
11)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
0
else
18)
else
(if i.val < 2083 then
11
else
17))
else
(if i.val < 2086 then
(if i.val < 2085 then
0
else
0)
else
(if i.val < 2087 then
0
else
31)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
0
else
0)
else
(if i.val < 2091 then
28
else
16))
else
(if i.val < 2094 then
(if i.val < 2093 then
16
else
0)
else
(if i.val < 2095 then
0
else
32))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
18
else
28)
else
(if i.val < 2099 then
0
else
22))
else
(if i.val < 2102 then
(if i.val < 2101 then
0
else
0)
else
(if i.val < 2103 then
11
else
35)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
24
else
18)
else
(if i.val < 2107 then
0
else
0))
else
(if i.val < 2110 then
(if i.val < 2109 then
21
else
0)
else
(if i.val < 2111 then
22
else
0))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
0
else
26)
else
(if i.val < 2115 then
21
else
25))
else
(if i.val < 2118 then
(if i.val < 2117 then
23
else
22)
else
(if i.val < 2119 then
22
else
24)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
0
else
8)
else
(if i.val < 2123 then
0
else
0))
else
(if i.val < 2126 then
(if i.val < 2125 then
21
else
19)
else
(if i.val < 2127 then
0
else
10))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
0
else
29)
else
(if i.val < 2131 then
13
else
0))
else
(if i.val < 2134 then
(if i.val < 2133 then
0
else
0)
else
(if i.val < 2135 then
0
else
0)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
0
else
0)
else
(if i.val < 2139 then
0
else
0))
else
(if i.val < 2142 then
(if i.val < 2141 then
0
else
0)
else
(if i.val < 2143 then
27
else
0)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
0
else
0)
else
(if i.val < 2147 then
10
else
35))
else
(if i.val < 2150 then
(if i.val < 2149 then
32
else
10)
else
(if i.val < 2151 then
0
else
0)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
0
else
0)
else
(if i.val < 2155 then
0
else
0))
else
(if i.val < 2158 then
(if i.val < 2157 then
22
else
12)
else
(if i.val < 2159 then
20
else
29))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
0
else
8)
else
(if i.val < 2163 then
22
else
0))
else
(if i.val < 2166 then
(if i.val < 2165 then
0
else
0)
else
(if i.val < 2167 then
8
else
22)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
0
else
0)
else
(if i.val < 2171 then
0
else
23))
else
(if i.val < 2174 then
(if i.val < 2173 then
0
else
25)
else
(if i.val < 2175 then
23
else
22)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
8
else
0)
else
(if i.val < 2179 then
0
else
35))
else
(if i.val < 2182 then
(if i.val < 2181 then
0
else
0)
else
(if i.val < 2183 then
21
else
8)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
0
else
0)
else
(if i.val < 2187 then
23
else
0))
else
(if i.val < 2190 then
(if i.val < 2189 then
4
else
20)
else
(if i.val < 2191 then
23
else
4))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
0
else
23)
else
(if i.val < 2195 then
22
else
23))
else
(if i.val < 2198 then
(if i.val < 2197 then
23
else
8)
else
(if i.val < 2199 then
8
else
21)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
4
else
8)
else
(if i.val < 2203 then
0
else
0))
else
(if i.val < 2206 then
(if i.val < 2205 then
28
else
8)
else
(if i.val < 2207 then
0
else
35)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
18
else
20)
else
(if i.val < 2211 then
16
else
0))
else
(if i.val < 2214 then
(if i.val < 2213 then
0
else
25)
else
(if i.val < 2215 then
25
else
11)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
19
else
0)
else
(if i.val < 2219 then
32
else
31))
else
(if i.val < 2222 then
(if i.val < 2221 then
28
else
27)
else
(if i.val < 2223 then
10
else
27))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
0
else
14)
else
(if i.val < 2227 then
14
else
11))
else
(if i.val < 2230 then
(if i.val < 2229 then
0
else
11)
else
(if i.val < 2231 then
0
else
14)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
21
else
12)
else
(if i.val < 2235 then
18
else
14))
else
(if i.val < 2238 then
(if i.val < 2237 then
32
else
0)
else
(if i.val < 2239 then
11
else
27))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
0
else
0)
else
(if i.val < 2243 then
18
else
14))
else
(if i.val < 2246 then
(if i.val < 2245 then
0
else
18)
else
(if i.val < 2247 then
0
else
0)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
0
else
0)
else
(if i.val < 2251 then
0
else
0))
else
(if i.val < 2254 then
(if i.val < 2253 then
0
else
0)
else
(if i.val < 2255 then
0
else
0))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
0
else
0)
else
(if i.val < 2259 then
0
else
0))
else
(if i.val < 2262 then
(if i.val < 2261 then
0
else
0)
else
(if i.val < 2263 then
0
else
0)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
0
else
0)
else
(if i.val < 2267 then
0
else
0))
else
(if i.val < 2270 then
(if i.val < 2269 then
0
else
0)
else
(if i.val < 2271 then
0
else
11)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
0
else
0)
else
(if i.val < 2275 then
12
else
14))
else
(if i.val < 2278 then
(if i.val < 2277 then
28
else
32)
else
(if i.val < 2279 then
1
else
14)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
0
else
27)
else
(if i.val < 2283 then
0
else
10))
else
(if i.val < 2286 then
(if i.val < 2285 then
0
else
33)
else
(if i.val < 2287 then
0
else
25))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
21
else
29)
else
(if i.val < 2291 then
10
else
19))
else
(if i.val < 2294 then
(if i.val < 2293 then
18
else
0)
else
(if i.val < 2295 then
0
else
0)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
27
else
10)
else
(if i.val < 2299 then
11
else
0))
else
(if i.val < 2302 then
(if i.val < 2301 then
11
else
27)
else
(if i.val < 2303 then
31
else
14))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
14
else
29)
else
(if i.val < 2307 then
27
else
0))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
0)
else
(if i.val < 2311 then
5
else
20)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
12
else
0)
else
(if i.val < 2315 then
10
else
24))
else
(if i.val < 2318 then
(if i.val < 2317 then
25
else
0)
else
(if i.val < 2319 then
26
else
0))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
0
else
0)
else
(if i.val < 2323 then
12
else
2))
else
(if i.val < 2326 then
(if i.val < 2325 then
0
else
23)
else
(if i.val < 2327 then
0
else
32)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
28
else
0)
else
(if i.val < 2331 then
23
else
33))
else
(if i.val < 2334 then
(if i.val < 2333 then
21
else
22)
else
(if i.val < 2335 then
0
else
17)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
26
else
35)
else
(if i.val < 2339 then
0
else
29))
else
(if i.val < 2342 then
(if i.val < 2341 then
11
else
29)
else
(if i.val < 2343 then
22
else
23)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
8
else
12)
else
(if i.val < 2347 then
0
else
0))
else
(if i.val < 2350 then
(if i.val < 2349 then
26
else
0)
else
(if i.val < 2351 then
0
else
10))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
25
else
0)
else
(if i.val < 2355 then
0
else
21))
else
(if i.val < 2358 then
(if i.val < 2357 then
22
else
5)
else
(if i.val < 2359 then
0
else
6)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
6
else
29)
else
(if i.val < 2363 then
5
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
0
else
12)
else
(if i.val < 2367 then
0
else
0))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
6
else
10)
else
(if i.val < 2371 then
27
else
0))
else
(if i.val < 2374 then
(if i.val < 2373 then
0
else
0)
else
(if i.val < 2375 then
18
else
11)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
0
else
0)
else
(if i.val < 2379 then
1
else
0))
else
(if i.val < 2382 then
(if i.val < 2381 then
31
else
0)
else
(if i.val < 2383 then
18
else
0))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
0
else
32)
else
(if i.val < 2387 then
6
else
22))
else
(if i.val < 2390 then
(if i.val < 2389 then
0
else
0)
else
(if i.val < 2391 then
8
else
33)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
6
else
0)
else
(if i.val < 2395 then
0
else
0))
else
(if i.val < 2398 then
(if i.val < 2397 then
35
else
8)
else
(if i.val < 2399 then
22
else
34)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
0
else
8)
else
(if i.val < 2403 then
6
else
9))
else
(if i.val < 2406 then
(if i.val < 2405 then
10
else
33)
else
(if i.val < 2407 then
10
else
18)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
29
else
10)
else
(if i.val < 2411 then
12
else
27))
else
(if i.val < 2414 then
(if i.val < 2413 then
10
else
29)
else
(if i.val < 2415 then
29
else
8))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
0
else
23)
else
(if i.val < 2419 then
0
else
0))
else
(if i.val < 2422 then
(if i.val < 2421 then
0
else
27)
else
(if i.val < 2423 then
8
else
0)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
0
else
14)
else
(if i.val < 2427 then
0
else
14))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
26)
else
(if i.val < 2431 then
8
else
11)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
10
else
0)
else
(if i.val < 2435 then
8
else
10))
else
(if i.val < 2438 then
(if i.val < 2437 then
0
else
0)
else
(if i.val < 2439 then
0
else
0)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
12
else
0)
else
(if i.val < 2443 then
8
else
0))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
23)
else
(if i.val < 2447 then
8
else
32))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
0
else
0)
else
(if i.val < 2451 then
28
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
23
else
10)
else
(if i.val < 2455 then
19
else
23)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
23
else
12)
else
(if i.val < 2459 then
0
else
21))
else
(if i.val < 2462 then
(if i.val < 2461 then
29
else
24)
else
(if i.val < 2463 then
8
else
0)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
23
else
22)
else
(if i.val < 2467 then
25
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
25
else
0)
else
(if i.val < 2471 then
21
else
0)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
20
else
14)
else
(if i.val < 2475 then
0
else
7))
else
(if i.val < 2478 then
(if i.val < 2477 then
8
else
23)
else
(if i.val < 2479 then
0
else
24))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
9
else
6)
else
(if i.val < 2483 then
33
else
24))
else
(if i.val < 2486 then
(if i.val < 2485 then
24
else
8)
else
(if i.val < 2487 then
13
else
2)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
8
else
34)
else
(if i.val < 2491 then
25
else
8))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
25)
else
(if i.val < 2495 then
17
else
24))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
21
else
8)
else
(if i.val < 2499 then
32
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
14
else
32)
else
(if i.val < 2503 then
22
else
19)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
24
else
0)
else
(if i.val < 2507 then
0
else
35))
else
(if i.val < 2510 then
(if i.val < 2509 then
32
else
0)
else
(if i.val < 2511 then
0
else
23))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
22
else
26)
else
(if i.val < 2515 then
0
else
0))
else
(if i.val < 2518 then
(if i.val < 2517 then
21
else
6)
else
(if i.val < 2519 then
25
else
0)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
17
else
0)
else
(if i.val < 2523 then
31
else
31))
else
(if i.val < 2526 then
(if i.val < 2525 then
2
else
18)
else
(if i.val < 2527 then
14
else
18)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
0
else
8)
else
(if i.val < 2531 then
8
else
21))
else
(if i.val < 2534 then
(if i.val < 2533 then
16
else
12)
else
(if i.val < 2535 then
0
else
0)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
9
else
32)
else
(if i.val < 2539 then
9
else
32))
else
(if i.val < 2542 then
(if i.val < 2541 then
0
else
0)
else
(if i.val < 2543 then
31
else
0))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
0
else
25)
else
(if i.val < 2547 then
0
else
18))
else
(if i.val < 2550 then
(if i.val < 2549 then
16
else
0)
else
(if i.val < 2551 then
31
else
8)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
0
else
8)
else
(if i.val < 2555 then
0
else
0))
else
(if i.val < 2558 then
(if i.val < 2557 then
0
else
12)
else
(if i.val < 2559 then
0
else
31)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0005 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
22
else
14)
else
(if i.val < 2563 then
9
else
0))
else
(if i.val < 2566 then
(if i.val < 2565 then
17
else
0)
else
(if i.val < 2567 then
0
else
0)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
0
else
0)
else
(if i.val < 2571 then
0
else
18))
else
(if i.val < 2574 then
(if i.val < 2573 then
32
else
14)
else
(if i.val < 2575 then
0
else
32))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
0
else
18)
else
(if i.val < 2579 then
0
else
20))
else
(if i.val < 2582 then
(if i.val < 2581 then
17
else
5)
else
(if i.val < 2583 then
11
else
0)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
18
else
30)
else
(if i.val < 2587 then
0
else
11))
else
(if i.val < 2590 then
(if i.val < 2589 then
0
else
6)
else
(if i.val < 2591 then
8
else
1)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
18
else
0)
else
(if i.val < 2595 then
25
else
25))
else
(if i.val < 2598 then
(if i.val < 2597 then
17
else
24)
else
(if i.val < 2599 then
1
else
19)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
25
else
35)
else
(if i.val < 2603 then
21
else
8))
else
(if i.val < 2606 then
(if i.val < 2605 then
6
else
25)
else
(if i.val < 2607 then
8
else
25))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
23
else
22)
else
(if i.val < 2611 then
0
else
7))
else
(if i.val < 2614 then
(if i.val < 2613 then
8
else
2)
else
(if i.val < 2615 then
0
else
0)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
23
else
25)
else
(if i.val < 2619 then
8
else
0))
else
(if i.val < 2622 then
(if i.val < 2621 then
14
else
0)
else
(if i.val < 2623 then
19
else
0))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
11
else
0)
else
(if i.val < 2627 then
10
else
0))
else
(if i.val < 2630 then
(if i.val < 2629 then
0
else
0)
else
(if i.val < 2631 then
0
else
0)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
0
else
0)
else
(if i.val < 2635 then
0
else
0))
else
(if i.val < 2638 then
(if i.val < 2637 then
0
else
0)
else
(if i.val < 2639 then
0
else
0))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
24)
else
(if i.val < 2643 then
33
else
0))
else
(if i.val < 2646 then
(if i.val < 2645 then
0
else
0)
else
(if i.val < 2647 then
11
else
11)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
18
else
10)
else
(if i.val < 2651 then
27
else
0))
else
(if i.val < 2654 then
(if i.val < 2653 then
8
else
0)
else
(if i.val < 2655 then
0
else
27)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
22
else
0)
else
(if i.val < 2659 then
22
else
5))
else
(if i.val < 2662 then
(if i.val < 2661 then
8
else
35)
else
(if i.val < 2663 then
22
else
8)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
25
else
35)
else
(if i.val < 2667 then
22
else
0))
else
(if i.val < 2670 then
(if i.val < 2669 then
24
else
35)
else
(if i.val < 2671 then
0
else
23))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
8
else
25)
else
(if i.val < 2675 then
23
else
23))
else
(if i.val < 2678 then
(if i.val < 2677 then
0
else
14)
else
(if i.val < 2679 then
0
else
0)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
8
else
22)
else
(if i.val < 2683 then
23
else
23))
else
(if i.val < 2686 then
(if i.val < 2685 then
22
else
8)
else
(if i.val < 2687 then
35
else
35)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
9
else
0)
else
(if i.val < 2691 then
20
else
24))
else
(if i.val < 2694 then
(if i.val < 2693 then
6
else
35)
else
(if i.val < 2695 then
21
else
0)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
0
else
8)
else
(if i.val < 2699 then
11
else
0))
else
(if i.val < 2702 then
(if i.val < 2701 then
26
else
0)
else
(if i.val < 2703 then
6
else
8))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
26
else
25)
else
(if i.val < 2707 then
8
else
8))
else
(if i.val < 2710 then
(if i.val < 2709 then
0
else
27)
else
(if i.val < 2711 then
23
else
23)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
23
else
25)
else
(if i.val < 2715 then
0
else
23))
else
(if i.val < 2718 then
(if i.val < 2717 then
23
else
23)
else
(if i.val < 2719 then
0
else
24)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
0
else
35)
else
(if i.val < 2723 then
32
else
23))
else
(if i.val < 2726 then
(if i.val < 2725 then
23
else
22)
else
(if i.val < 2727 then
23
else
23)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
24
else
23)
else
(if i.val < 2731 then
22
else
5))
else
(if i.val < 2734 then
(if i.val < 2733 then
21
else
25)
else
(if i.val < 2735 then
24
else
35))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
22
else
22)
else
(if i.val < 2739 then
24
else
24))
else
(if i.val < 2742 then
(if i.val < 2741 then
25
else
8)
else
(if i.val < 2743 then
29
else
17)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
28
else
19)
else
(if i.val < 2747 then
23
else
0))
else
(if i.val < 2750 then
(if i.val < 2749 then
21
else
33)
else
(if i.val < 2751 then
5
else
18))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
32
else
21)
else
(if i.val < 2755 then
31
else
14))
else
(if i.val < 2758 then
(if i.val < 2757 then
0
else
0)
else
(if i.val < 2759 then
11
else
27)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
28
else
14)
else
(if i.val < 2763 then
0
else
9))
else
(if i.val < 2766 then
(if i.val < 2765 then
18
else
0)
else
(if i.val < 2767 then
32
else
28))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
13
else
12)
else
(if i.val < 2771 then
0
else
10))
else
(if i.val < 2774 then
(if i.val < 2773 then
31
else
11)
else
(if i.val < 2775 then
18
else
28)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
11
else
14)
else
(if i.val < 2779 then
14
else
14))
else
(if i.val < 2782 then
(if i.val < 2781 then
31
else
11)
else
(if i.val < 2783 then
11
else
14)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
9
else
0)
else
(if i.val < 2787 then
31
else
14))
else
(if i.val < 2790 then
(if i.val < 2789 then
29
else
18)
else
(if i.val < 2791 then
0
else
11)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
1
else
0)
else
(if i.val < 2795 then
18
else
18))
else
(if i.val < 2798 then
(if i.val < 2797 then
33
else
11)
else
(if i.val < 2799 then
0
else
0))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
1
else
14)
else
(if i.val < 2803 then
0
else
18))
else
(if i.val < 2806 then
(if i.val < 2805 then
16
else
25)
else
(if i.val < 2807 then
0
else
28)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
32
else
14)
else
(if i.val < 2811 then
18
else
11))
else
(if i.val < 2814 then
(if i.val < 2813 then
0
else
0)
else
(if i.val < 2815 then
0
else
0))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
0
else
0)
else
(if i.val < 2819 then
0
else
0))
else
(if i.val < 2822 then
(if i.val < 2821 then
0
else
0)
else
(if i.val < 2823 then
0
else
0)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
0
else
0)
else
(if i.val < 2827 then
0
else
0))
else
(if i.val < 2830 then
(if i.val < 2829 then
0
else
0)
else
(if i.val < 2831 then
0
else
0))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
0
else
0)
else
(if i.val < 2835 then
0
else
0))
else
(if i.val < 2838 then
(if i.val < 2837 then
0
else
0)
else
(if i.val < 2839 then
0
else
0)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
0
else
0)
else
(if i.val < 2843 then
0
else
0))
else
(if i.val < 2846 then
(if i.val < 2845 then
10
else
11)
else
(if i.val < 2847 then
11
else
0)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
0
else
0)
else
(if i.val < 2851 then
8
else
0))
else
(if i.val < 2854 then
(if i.val < 2853 then
0
else
16)
else
(if i.val < 2855 then
13
else
30)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
14
else
1)
else
(if i.val < 2859 then
11
else
12))
else
(if i.val < 2862 then
(if i.val < 2861 then
0
else
31)
else
(if i.val < 2863 then
0
else
1))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
16
else
0)
else
(if i.val < 2867 then
0
else
20))
else
(if i.val < 2870 then
(if i.val < 2869 then
19
else
18)
else
(if i.val < 2871 then
10
else
16)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
21
else
0)
else
(if i.val < 2875 then
26
else
8))
else
(if i.val < 2878 then
(if i.val < 2877 then
0
else
33)
else
(if i.val < 2879 then
29
else
33))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
18
else
0)
else
(if i.val < 2883 then
16
else
5))
else
(if i.val < 2886 then
(if i.val < 2885 then
0
else
0)
else
(if i.val < 2887 then
27
else
11)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
12
else
14)
else
(if i.val < 2891 then
14
else
28))
else
(if i.val < 2894 then
(if i.val < 2893 then
28
else
11)
else
(if i.val < 2895 then
10
else
8))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
29
else
0)
else
(if i.val < 2899 then
0
else
0))
else
(if i.val < 2902 then
(if i.val < 2901 then
35
else
0)
else
(if i.val < 2903 then
9
else
27)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
0
else
8)
else
(if i.val < 2907 then
0
else
25))
else
(if i.val < 2910 then
(if i.val < 2909 then
6
else
12)
else
(if i.val < 2911 then
5
else
20)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
25
else
0)
else
(if i.val < 2915 then
0
else
8))
else
(if i.val < 2918 then
(if i.val < 2917 then
35
else
0)
else
(if i.val < 2919 then
18
else
0)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
0
else
0)
else
(if i.val < 2923 then
0
else
19))
else
(if i.val < 2926 then
(if i.val < 2925 then
24
else
0)
else
(if i.val < 2927 then
13
else
17))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
0
else
18)
else
(if i.val < 2931 then
5
else
6))
else
(if i.val < 2934 then
(if i.val < 2933 then
8
else
8)
else
(if i.val < 2935 then
17
else
21)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
0
else
35)
else
(if i.val < 2939 then
35
else
35))
else
(if i.val < 2942 then
(if i.val < 2941 then
33
else
0)
else
(if i.val < 2943 then
17
else
17)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
21
else
7)
else
(if i.val < 2947 then
0
else
8))
else
(if i.val < 2950 then
(if i.val < 2949 then
21
else
24)
else
(if i.val < 2951 then
17
else
24)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
0
else
0)
else
(if i.val < 2955 then
28
else
26))
else
(if i.val < 2958 then
(if i.val < 2957 then
23
else
6)
else
(if i.val < 2959 then
5
else
29))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
12
else
0)
else
(if i.val < 2963 then
27
else
0))
else
(if i.val < 2966 then
(if i.val < 2965 then
0
else
0)
else
(if i.val < 2967 then
8
else
0)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
7
else
0)
else
(if i.val < 2971 then
0
else
20))
else
(if i.val < 2974 then
(if i.val < 2973 then
29
else
5)
else
(if i.val < 2975 then
21
else
0)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
8
else
0)
else
(if i.val < 2979 then
22
else
8))
else
(if i.val < 2982 then
(if i.val < 2981 then
10
else
8)
else
(if i.val < 2983 then
26
else
0)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
35
else
32)
else
(if i.val < 2987 then
0
else
0))
else
(if i.val < 2990 then
(if i.val < 2989 then
29
else
17)
else
(if i.val < 2991 then
10
else
18))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
1
else
8)
else
(if i.val < 2995 then
0
else
30))
else
(if i.val < 2998 then
(if i.val < 2997 then
18
else
0)
else
(if i.val < 2999 then
0
else
14)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
0
else
14)
else
(if i.val < 3003 then
14
else
31))
else
(if i.val < 3006 then
(if i.val < 3005 then
0
else
32)
else
(if i.val < 3007 then
32
else
11))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
0
else
26)
else
(if i.val < 3011 then
19
else
32))
else
(if i.val < 3014 then
(if i.val < 3013 then
34
else
21)
else
(if i.val < 3015 then
26
else
35)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
35
else
6)
else
(if i.val < 3019 then
5
else
18))
else
(if i.val < 3022 then
(if i.val < 3021 then
10
else
27)
else
(if i.val < 3023 then
27
else
8))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
32
else
0)
else
(if i.val < 3027 then
0
else
27))
else
(if i.val < 3030 then
(if i.val < 3029 then
0
else
23)
else
(if i.val < 3031 then
22
else
12)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
32
else
29)
else
(if i.val < 3035 then
8
else
8))
else
(if i.val < 3038 then
(if i.val < 3037 then
23
else
32)
else
(if i.val < 3039 then
0
else
0)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
8
else
0)
else
(if i.val < 3043 then
14
else
18))
else
(if i.val < 3046 then
(if i.val < 3045 then
11
else
0)
else
(if i.val < 3047 then
0
else
0)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
0
else
31)
else
(if i.val < 3051 then
0
else
28))
else
(if i.val < 3054 then
(if i.val < 3053 then
18
else
5)
else
(if i.val < 3055 then
0
else
24))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
30
else
0)
else
(if i.val < 3059 then
23
else
22))
else
(if i.val < 3062 then
(if i.val < 3061 then
22
else
5)
else
(if i.val < 3063 then
0
else
0)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
0
else
29)
else
(if i.val < 3067 then
0
else
0))
else
(if i.val < 3070 then
(if i.val < 3069 then
0
else
0)
else
(if i.val < 3071 then
9
else
35)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0006 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
0
else
32)
else
(if i.val < 3075 then
10
else
0))
else
(if i.val < 3078 then
(if i.val < 3077 then
35
else
0)
else
(if i.val < 3079 then
29
else
8)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
5
else
0)
else
(if i.val < 3083 then
23
else
0))
else
(if i.val < 3086 then
(if i.val < 3085 then
22
else
0)
else
(if i.val < 3087 then
8
else
0))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
0
else
21)
else
(if i.val < 3091 then
8
else
0))
else
(if i.val < 3094 then
(if i.val < 3093 then
0
else
24)
else
(if i.val < 3095 then
0
else
4)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
18
else
8)
else
(if i.val < 3099 then
23
else
8))
else
(if i.val < 3102 then
(if i.val < 3101 then
0
else
21)
else
(if i.val < 3103 then
20
else
8)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
5
else
35)
else
(if i.val < 3107 then
16
else
0))
else
(if i.val < 3110 then
(if i.val < 3109 then
25
else
11)
else
(if i.val < 3111 then
19
else
32)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
32
else
13)
else
(if i.val < 3115 then
10
else
27))
else
(if i.val < 3118 then
(if i.val < 3117 then
11
else
11)
else
(if i.val < 3119 then
30
else
11))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
21
else
18)
else
(if i.val < 3123 then
32
else
1))
else
(if i.val < 3126 then
(if i.val < 3125 then
27
else
0)
else
(if i.val < 3127 then
13
else
18)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
4
else
11)
else
(if i.val < 3131 then
18
else
0))
else
(if i.val < 3134 then
(if i.val < 3133 then
0
else
0)
else
(if i.val < 3135 then
0
else
0))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
0
else
0)
else
(if i.val < 3139 then
0
else
0))
else
(if i.val < 3142 then
(if i.val < 3141 then
0
else
0)
else
(if i.val < 3143 then
11
else
27)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
12
else
32)
else
(if i.val < 3147 then
14
else
0))
else
(if i.val < 3150 then
(if i.val < 3149 then
27
else
0)
else
(if i.val < 3151 then
5
else
12))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
19
else
13)
else
(if i.val < 3155 then
10
else
11))
else
(if i.val < 3158 then
(if i.val < 3157 then
27
else
13)
else
(if i.val < 3159 then
11
else
0)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
0
else
5)
else
(if i.val < 3163 then
20
else
12))
else
(if i.val < 3166 then
(if i.val < 3165 then
10
else
35)
else
(if i.val < 3167 then
0
else
26)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
21
else
8)
else
(if i.val < 3171 then
21
else
22))
else
(if i.val < 3174 then
(if i.val < 3173 then
0
else
17)
else
(if i.val < 3175 then
26
else
35)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
12
else
6)
else
(if i.val < 3179 then
29
else
29))
else
(if i.val < 3182 then
(if i.val < 3181 then
25
else
0)
else
(if i.val < 3183 then
22
else
21))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
6
else
29)
else
(if i.val < 3187 then
10
else
26))
else
(if i.val < 3190 then
(if i.val < 3189 then
8
else
6)
else
(if i.val < 3191 then
0
else
0)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
11
else
0)
else
(if i.val < 3195 then
0
else
18))
else
(if i.val < 3198 then
(if i.val < 3197 then
20
else
32)
else
(if i.val < 3199 then
6
else
22)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
20
else
21)
else
(if i.val < 3203 then
1
else
5))
else
(if i.val < 3206 then
(if i.val < 3205 then
8
else
34)
else
(if i.val < 3207 then
8
else
8)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
33
else
10)
else
(if i.val < 3211 then
18
else
12))
else
(if i.val < 3214 then
(if i.val < 3213 then
29
else
29)
else
(if i.val < 3215 then
23
else
0))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
10
else
8)
else
(if i.val < 3219 then
31
else
6))
else
(if i.val < 3222 then
(if i.val < 3221 then
29
else
12)
else
(if i.val < 3223 then
10
else
0)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
0
else
10)
else
(if i.val < 3227 then
0
else
12))
else
(if i.val < 3230 then
(if i.val < 3229 then
0
else
23)
else
(if i.val < 3231 then
29
else
32)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
0
else
33)
else
(if i.val < 3235 then
31
else
0))
else
(if i.val < 3238 then
(if i.val < 3237 then
23
else
10)
else
(if i.val < 3239 then
19
else
23)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
23
else
9)
else
(if i.val < 3243 then
0
else
29))
else
(if i.val < 3246 then
(if i.val < 3245 then
24
else
23)
else
(if i.val < 3247 then
23
else
22))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
0
else
20)
else
(if i.val < 3251 then
14
else
22))
else
(if i.val < 3254 then
(if i.val < 3253 then
23
else
6)
else
(if i.val < 3255 then
33
else
24)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
4
else
4)
else
(if i.val < 3259 then
34
else
25))
else
(if i.val < 3262 then
(if i.val < 3261 then
6
else
23)
else
(if i.val < 3263 then
32
else
5))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
25
else
17)
else
(if i.val < 3267 then
31
else
2))
else
(if i.val < 3270 then
(if i.val < 3269 then
16
else
30)
else
(if i.val < 3271 then
18
else
8)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
21
else
13)
else
(if i.val < 3275 then
34
else
12))
else
(if i.val < 3278 then
(if i.val < 3277 then
32
else
9)
else
(if i.val < 3279 then
0
else
28))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
0
else
11)
else
(if i.val < 3283 then
11
else
34))
else
(if i.val < 3286 then
(if i.val < 3285 then
31
else
1)
else
(if i.val < 3287 then
8
else
0)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
12
else
6)
else
(if i.val < 3291 then
22
else
27))
else
(if i.val < 3294 then
(if i.val < 3293 then
9
else
27)
else
(if i.val < 3295 then
21
else
0)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
27
else
0)
else
(if i.val < 3299 then
0
else
13))
else
(if i.val < 3302 then
(if i.val < 3301 then
0
else
32)
else
(if i.val < 3303 then
18
else
0)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
22
else
11)
else
(if i.val < 3307 then
20
else
18))
else
(if i.val < 3310 then
(if i.val < 3309 then
30
else
20)
else
(if i.val < 3311 then
6
else
8))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
1
else
18)
else
(if i.val < 3315 then
35
else
25))
else
(if i.val < 3318 then
(if i.val < 3317 then
23
else
1)
else
(if i.val < 3319 then
19
else
35)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
21
else
6)
else
(if i.val < 3323 then
23
else
8))
else
(if i.val < 3326 then
(if i.val < 3325 then
25
else
8)
else
(if i.val < 3327 then
2
else
0))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
23
else
23)
else
(if i.val < 3331 then
8
else
4))
else
(if i.val < 3334 then
(if i.val < 3333 then
30
else
19)
else
(if i.val < 3335 then
33
else
11)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
10
else
0)
else
(if i.val < 3339 then
0
else
0))
else
(if i.val < 3342 then
(if i.val < 3341 then
0
else
0)
else
(if i.val < 3343 then
0
else
0))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
0
else
27)
else
(if i.val < 3347 then
33
else
32))
else
(if i.val < 3350 then
(if i.val < 3349 then
0
else
0)
else
(if i.val < 3351 then
11
else
11)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
18
else
10)
else
(if i.val < 3355 then
21
else
28))
else
(if i.val < 3358 then
(if i.val < 3357 then
0
else
27)
else
(if i.val < 3359 then
22
else
0)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
22
else
5)
else
(if i.val < 3363 then
23
else
22))
else
(if i.val < 3366 then
(if i.val < 3365 then
8
else
25)
else
(if i.val < 3367 then
22
else
23)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
35
else
0)
else
(if i.val < 3371 then
23
else
27))
else
(if i.val < 3374 then
(if i.val < 3373 then
23
else
4)
else
(if i.val < 3375 then
14
else
0))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
29
else
8)
else
(if i.val < 3379 then
22
else
23))
else
(if i.val < 3382 then
(if i.val < 3381 then
22
else
8)
else
(if i.val < 3383 then
35
else
10)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
13
else
20)
else
(if i.val < 3387 then
6
else
35))
else
(if i.val < 3390 then
(if i.val < 3389 then
21
else
0)
else
(if i.val < 3391 then
23
else
8))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
11
else
23)
else
(if i.val < 3395 then
23
else
0))
else
(if i.val < 3398 then
(if i.val < 3397 then
4
else
23)
else
(if i.val < 3399 then
23
else
4)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
23
else
24)
else
(if i.val < 3403 then
23
else
22))
else
(if i.val < 3406 then
(if i.val < 3405 then
5
else
21)
else
(if i.val < 3407 then
4
else
22))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
4
else
25)
else
(if i.val < 3411 then
8
else
29))
else
(if i.val < 3414 then
(if i.val < 3413 then
19
else
0)
else
(if i.val < 3415 then
0
else
12)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
5
else
5)
else
(if i.val < 3419 then
18
else
16))
else
(if i.val < 3422 then
(if i.val < 3421 then
6
else
11)
else
(if i.val < 3423 then
27
else
31)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
31
else
12)
else
(if i.val < 3427 then
0
else
10))
else
(if i.val < 3430 then
(if i.val < 3429 then
31
else
11)
else
(if i.val < 3431 then
18
else
28)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
14
else
14)
else
(if i.val < 3435 then
31
else
33))
else
(if i.val < 3438 then
(if i.val < 3437 then
32
else
13)
else
(if i.val < 3439 then
30
else
29))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
0
else
11)
else
(if i.val < 3443 then
16
else
18))
else
(if i.val < 3446 then
(if i.val < 3445 then
18
else
33)
else
(if i.val < 3447 then
1
else
32)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
0
else
31)
else
(if i.val < 3451 then
14
else
0))
else
(if i.val < 3454 then
(if i.val < 3453 then
0
else
0)
else
(if i.val < 3455 then
0
else
0)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
0
else
0)
else
(if i.val < 3459 then
0
else
0))
else
(if i.val < 3462 then
(if i.val < 3461 then
0
else
0)
else
(if i.val < 3463 then
0
else
0)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
0
else
0)
else
(if i.val < 3467 then
0
else
0))
else
(if i.val < 3470 then
(if i.val < 3469 then
0
else
11)
else
(if i.val < 3471 then
18
else
33))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
16
else
14)
else
(if i.val < 3475 then
30
else
14))
else
(if i.val < 3478 then
(if i.val < 3477 then
12
else
16)
else
(if i.val < 3479 then
20
else
26)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
21
else
35)
else
(if i.val < 3483 then
26
else
21))
else
(if i.val < 3486 then
(if i.val < 3485 then
0
else
33)
else
(if i.val < 3487 then
18
else
0)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
16
else
21)
else
(if i.val < 3491 then
27
else
12))
else
(if i.val < 3494 then
(if i.val < 3493 then
30
else
28)
else
(if i.val < 3495 then
11
else
8)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
29
else
29)
else
(if i.val < 3499 then
0
else
6))
else
(if i.val < 3502 then
(if i.val < 3501 then
35
else
8)
else
(if i.val < 3503 then
0
else
25))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
9
else
0)
else
(if i.val < 3507 then
20
else
0))
else
(if i.val < 3510 then
(if i.val < 3509 then
26
else
35)
else
(if i.val < 3511 then
22
else
18)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
21
else
0)
else
(if i.val < 3515 then
0
else
23))
else
(if i.val < 3518 then
(if i.val < 3517 then
19
else
24)
else
(if i.val < 3519 then
0
else
35))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
22
else
17)
else
(if i.val < 3523 then
26
else
0))
else
(if i.val < 3526 then
(if i.val < 3525 then
22
else
21)
else
(if i.val < 3527 then
11
else
24)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
0
else
28)
else
(if i.val < 3531 then
23
else
5))
else
(if i.val < 3534 then
(if i.val < 3533 then
0
else
12)
else
(if i.val < 3535 then
6
else
27))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
23
else
0)
else
(if i.val < 3539 then
8
else
7))
else
(if i.val < 3542 then
(if i.val < 3541 then
27
else
20)
else
(if i.val < 3543 then
5
else
21)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
0
else
8)
else
(if i.val < 3547 then
0
else
22))
else
(if i.val < 3550 then
(if i.val < 3549 then
10
else
35)
else
(if i.val < 3551 then
32
else
0)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
0
else
17)
else
(if i.val < 3555 then
18
else
0))
else
(if i.val < 3558 then
(if i.val < 3557 then
30
else
20)
else
(if i.val < 3559 then
14
else
14)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
26
else
0)
else
(if i.val < 3563 then
32
else
32))
else
(if i.val < 3566 then
(if i.val < 3565 then
0
else
26)
else
(if i.val < 3567 then
19
else
32))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
34
else
23)
else
(if i.val < 3571 then
19
else
25))
else
(if i.val < 3574 then
(if i.val < 3573 then
22
else
0)
else
(if i.val < 3575 then
21
else
35)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
8
else
8)
else
(if i.val < 3579 then
25
else
26))
else
(if i.val < 3582 then
(if i.val < 3581 then
8
else
32)
else
(if i.val < 3583 then
0
else
18)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0007 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
33
else
6)
else
(if i.val < 3587 then
16
else
18))
else
(if i.val < 3590 then
(if i.val < 3589 then
33
else
10)
else
(if i.val < 3591 then
26
else
26)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
13
else
11)
else
(if i.val < 3595 then
9
else
12))
else
(if i.val < 3598 then
(if i.val < 3597 then
26
else
28)
else
(if i.val < 3599 then
10
else
28))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
8
else
32)
else
(if i.val < 3603 then
0
else
18))
else
(if i.val < 3606 then
(if i.val < 3605 then
10
else
27)
else
(if i.val < 3607 then
27
else
8)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
0
else
10)
else
(if i.val < 3611 then
23
else
27))
else
(if i.val < 3614 then
(if i.val < 3613 then
0
else
0)
else
(if i.val < 3615 then
12
else
10)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
29
else
26)
else
(if i.val < 3619 then
12
else
23))
else
(if i.val < 3622 then
(if i.val < 3621 then
27
else
32)
else
(if i.val < 3623 then
31
else
22)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
1
else
0)
else
(if i.val < 3627 then
19
else
20))
else
(if i.val < 3630 then
(if i.val < 3629 then
17
else
8)
else
(if i.val < 3631 then
33
else
14))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
32
else
1)
else
(if i.val < 3635 then
4
else
23))
else
(if i.val < 3638 then
(if i.val < 3637 then
23
else
0)
else
(if i.val < 3639 then
26
else
10)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
31
else
34)
else
(if i.val < 3643 then
29
else
31))
else
(if i.val < 3646 then
(if i.val < 3645 then
8
else
2)
else
(if i.val < 3647 then
29
else
10))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
0
else
0)
else
(if i.val < 3651 then
24
else
22))
else
(if i.val < 3654 then
(if i.val < 3653 then
25
else
14)
else
(if i.val < 3655 then
14
else
20)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
34
else
26)
else
(if i.val < 3659 then
19
else
8))
else
(if i.val < 3662 then
(if i.val < 3661 then
23
else
22)
else
(if i.val < 3663 then
22
else
31))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
19
else
0)
else
(if i.val < 3667 then
20
else
17))
else
(if i.val < 3670 then
(if i.val < 3669 then
17
else
19)
else
(if i.val < 3671 then
18
else
14)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
31
else
1)
else
(if i.val < 3675 then
10
else
0))
else
(if i.val < 3678 then
(if i.val < 3677 then
32
else
11)
else
(if i.val < 3679 then
22
else
32)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
21
else
6)
else
(if i.val < 3683 then
24
else
32))
else
(if i.val < 3686 then
(if i.val < 3685 then
5
else
1)
else
(if i.val < 3687 then
26
else
18)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
30
else
28)
else
(if i.val < 3691 then
23
else
18))
else
(if i.val < 3694 then
(if i.val < 3693 then
30
else
16)
else
(if i.val < 3695 then
18
else
31))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
11
else
13)
else
(if i.val < 3699 then
4
else
1))
else
(if i.val < 3702 then
(if i.val < 3701 then
15
else
14)
else
(if i.val < 3703 then
8
else
9)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
11
else
35)
else
(if i.val < 3707 then
8
else
17))
else
(if i.val < 3710 then
(if i.val < 3709 then
17
else
19)
else
(if i.val < 3711 then
12
else
18)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
14
else
30)
else
(if i.val < 3715 then
0
else
19))
else
(if i.val < 3718 then
(if i.val < 3717 then
14
else
27)
else
(if i.val < 3719 then
12
else
2)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
18
else
1)
else
(if i.val < 3723 then
0
else
0))
else
(if i.val < 3726 then
(if i.val < 3725 then
0
else
16)
else
(if i.val < 3727 then
18
else
14))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
0
else
24)
else
(if i.val < 3731 then
1
else
20))
else
(if i.val < 3734 then
(if i.val < 3733 then
35
else
0)
else
(if i.val < 3735 then
20
else
17)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
5
else
25)
else
(if i.val < 3739 then
19
else
25))
else
(if i.val < 3742 then
(if i.val < 3741 then
25
else
21)
else
(if i.val < 3743 then
23
else
32)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
18
else
29)
else
(if i.val < 3747 then
16
else
0))
else
(if i.val < 3750 then
(if i.val < 3749 then
22
else
14)
else
(if i.val < 3751 then
34
else
28)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
3
else
6)
else
(if i.val < 3755 then
11
else
33))
else
(if i.val < 3758 then
(if i.val < 3757 then
10
else
12)
else
(if i.val < 3759 then
0
else
0))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
0
else
0)
else
(if i.val < 3763 then
0
else
0))
else
(if i.val < 3766 then
(if i.val < 3765 then
0
else
0)
else
(if i.val < 3767 then
11
else
0)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
29
else
10)
else
(if i.val < 3771 then
0
else
11))
else
(if i.val < 3774 then
(if i.val < 3773 then
14
else
8)
else
(if i.val < 3775 then
8
else
22))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
0
else
1)
else
(if i.val < 3779 then
5
else
24))
else
(if i.val < 3782 then
(if i.val < 3781 then
8
else
0)
else
(if i.val < 3783 then
23
else
23)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
23
else
5)
else
(if i.val < 3787 then
0
else
14))
else
(if i.val < 3790 then
(if i.val < 3789 then
20
else
23)
else
(if i.val < 3791 then
23
else
34))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
22
else
23)
else
(if i.val < 3795 then
28
else
29))
else
(if i.val < 3798 then
(if i.val < 3797 then
24
else
27)
else
(if i.val < 3799 then
10
else
4)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
35
else
28)
else
(if i.val < 3803 then
26
else
34))
else
(if i.val < 3806 then
(if i.val < 3805 then
18
else
35)
else
(if i.val < 3807 then
35
else
25)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
25
else
35)
else
(if i.val < 3811 then
18
else
26))
else
(if i.val < 3814 then
(if i.val < 3813 then
0
else
0)
else
(if i.val < 3815 then
23
else
23)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
7
else
23)
else
(if i.val < 3819 then
25
else
22))
else
(if i.val < 3822 then
(if i.val < 3821 then
23
else
5)
else
(if i.val < 3823 then
35
else
8))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
22
else
22)
else
(if i.val < 3827 then
25
else
5))
else
(if i.val < 3830 then
(if i.val < 3829 then
8
else
22)
else
(if i.val < 3831 then
0
else
24)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
19
else
28)
else
(if i.val < 3835 then
16
else
28))
else
(if i.val < 3838 then
(if i.val < 3837 then
2
else
32)
else
(if i.val < 3839 then
13
else
32))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
14
else
0)
else
(if i.val < 3843 then
19
else
28))
else
(if i.val < 3846 then
(if i.val < 3845 then
1
else
18)
else
(if i.val < 3847 then
32
else
28)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
11
else
11)
else
(if i.val < 3851 then
27
else
11))
else
(if i.val < 3854 then
(if i.val < 3853 then
29
else
28)
else
(if i.val < 3855 then
31
else
11))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
14
else
14)
else
(if i.val < 3859 then
14
else
14))
else
(if i.val < 3862 then
(if i.val < 3861 then
11
else
18)
else
(if i.val < 3863 then
1
else
22)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
11
else
11)
else
(if i.val < 3867 then
11
else
3))
else
(if i.val < 3870 then
(if i.val < 3869 then
15
else
15)
else
(if i.val < 3871 then
1
else
29)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
18
else
0)
else
(if i.val < 3875 then
0
else
0))
else
(if i.val < 3878 then
(if i.val < 3877 then
0
else
0)
else
(if i.val < 3879 then
0
else
0)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
0
else
0)
else
(if i.val < 3883 then
0
else
0))
else
(if i.val < 3886 then
(if i.val < 3885 then
0
else
0)
else
(if i.val < 3887 then
0
else
0))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
0
else
0)
else
(if i.val < 3891 then
0
else
0))
else
(if i.val < 3894 then
(if i.val < 3893 then
0
else
0)
else
(if i.val < 3895 then
0
else
0)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
26
else
10)
else
(if i.val < 3899 then
11
else
26))
else
(if i.val < 3902 then
(if i.val < 3901 then
18
else
16)
else
(if i.val < 3903 then
34
else
32))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
30
else
30)
else
(if i.val < 3907 then
31
else
11))
else
(if i.val < 3910 then
(if i.val < 3909 then
12
else
31)
else
(if i.val < 3911 then
1
else
18)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
5
else
21)
else
(if i.val < 3915 then
21
else
26))
else
(if i.val < 3918 then
(if i.val < 3917 then
11
else
29)
else
(if i.val < 3919 then
8
else
17))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
0
else
22)
else
(if i.val < 3923 then
20
else
0))
else
(if i.val < 3926 then
(if i.val < 3925 then
11
else
11)
else
(if i.val < 3927 then
31
else
32)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
2
else
10)
else
(if i.val < 3931 then
27
else
6))
else
(if i.val < 3934 then
(if i.val < 3933 then
12
else
35)
else
(if i.val < 3935 then
5
else
18)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
6
else
18)
else
(if i.val < 3939 then
35
else
21))
else
(if i.val < 3942 then
(if i.val < 3941 then
5
else
19)
else
(if i.val < 3943 then
0
else
0)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
4
else
8)
else
(if i.val < 3947 then
35
else
35))
else
(if i.val < 3950 then
(if i.val < 3949 then
33
else
17)
else
(if i.val < 3951 then
31
else
22))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
0
else
17)
else
(if i.val < 3955 then
5
else
1))
else
(if i.val < 3958 then
(if i.val < 3957 then
0
else
28)
else
(if i.val < 3959 then
28
else
9)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
27
else
9)
else
(if i.val < 3963 then
0
else
7))
else
(if i.val < 3966 then
(if i.val < 3965 then
7
else
5)
else
(if i.val < 3967 then
23
else
33)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
23
else
34)
else
(if i.val < 3971 then
6
else
16))
else
(if i.val < 3974 then
(if i.val < 3973 then
33
else
0)
else
(if i.val < 3975 then
10
else
18)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
4
else
0)
else
(if i.val < 3979 then
30
else
7))
else
(if i.val < 3982 then
(if i.val < 3981 then
1
else
11)
else
(if i.val < 3983 then
30
else
34))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
20
else
1)
else
(if i.val < 3987 then
18
else
0))
else
(if i.val < 3990 then
(if i.val < 3989 then
20
else
18)
else
(if i.val < 3991 then
31
else
0)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
10
else
20)
else
(if i.val < 3995 then
23
else
20))
else
(if i.val < 3998 then
(if i.val < 3997 then
14
else
6)
else
(if i.val < 3999 then
24
else
25)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
24
else
0)
else
(if i.val < 4003 then
31
else
18))
else
(if i.val < 4006 then
(if i.val < 4005 then
13
else
22)
else
(if i.val < 4007 then
27
else
18)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
35
else
8)
else
(if i.val < 4011 then
24
else
25))
else
(if i.val < 4014 then
(if i.val < 4013 then
0
else
0)
else
(if i.val < 4015 then
33
else
6))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
0
else
15)
else
(if i.val < 4019 then
16
else
21))
else
(if i.val < 4022 then
(if i.val < 4021 then
28
else
23)
else
(if i.val < 4023 then
8
else
25)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
23
else
4)
else
(if i.val < 4027 then
14
else
22))
else
(if i.val < 4030 then
(if i.val < 4029 then
8
else
10)
else
(if i.val < 4031 then
13
else
25))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
25
else
23)
else
(if i.val < 4035 then
23
else
22))
else
(if i.val < 4038 then
(if i.val < 4037 then
0
else
30)
else
(if i.val < 4039 then
11
else
18)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
31
else
13)
else
(if i.val < 4043 then
9
else
13))
else
(if i.val < 4046 then
(if i.val < 4045 then
11
else
15)
else
(if i.val < 4047 then
33
else
1))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
11
else
0)
else
(if i.val < 4051 then
0
else
0))
else
(if i.val < 4054 then
(if i.val < 4053 then
0
else
12)
else
(if i.val < 4055 then
18
else
16)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
0
else
21)
else
(if i.val < 4059 then
29
else
14))
else
(if i.val < 4062 then
(if i.val < 4061 then
35
else
0)
else
(if i.val < 4063 then
20
else
21)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
8
else
26)
else
(if i.val < 4067 then
22
else
24))
else
(if i.val < 4070 then
(if i.val < 4069 then
0
else
30)
else
(if i.val < 4071 then
20
else
35)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
22
else
0)
else
(if i.val < 4075 then
20
else
1))
else
(if i.val < 4078 then
(if i.val < 4077 then
23
else
25)
else
(if i.val < 4079 then
26
else
17))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
10
else
26)
else
(if i.val < 4083 then
14
else
0))
else
(if i.val < 4086 then
(if i.val < 4085 then
29
else
8)
else
(if i.val < 4087 then
12
else
32)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
31
else
17)
else
(if i.val < 4091 then
22
else
32))
else
(if i.val < 4094 then
(if i.val < 4093 then
4
else
21)
else
(if i.val < 4095 then
22
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn2Part0008 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
20
else
(if i.val < 4098 then
34
else
18))
else
(if i.val < 4101 then
(if i.val < 4100 then
31
else
31)
else
(if i.val < 4102 then
32
else
32)))
else
(if i.val < 4106 then
(if i.val < 4104 then
21
else
(if i.val < 4105 then
6
else
32))
else
(if i.val < 4108 then
(if i.val < 4107 then
32
else
5)
else
(if i.val < 4109 then
18
else
4))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
6
else
(if i.val < 4112 then
23
else
17))
else
(if i.val < 4115 then
(if i.val < 4114 then
3
else
34)
else
(if i.val < 4116 then
29
else
12)))
else
(if i.val < 4120 then
(if i.val < 4118 then
2
else
(if i.val < 4119 then
1
else
0))
else
(if i.val < 4122 then
(if i.val < 4121 then
0
else
18)
else
(if i.val < 4123 then
14
else
20)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
0
else
(if i.val < 4126 then
20
else
17))
else
(if i.val < 4129 then
(if i.val < 4128 then
5
else
10)
else
(if i.val < 4130 then
19
else
6)))
else
(if i.val < 4134 then
(if i.val < 4132 then
18
else
(if i.val < 4133 then
14
else
3))
else
(if i.val < 4136 then
(if i.val < 4135 then
6
else
0)
else
(if i.val < 4137 then
0
else
0))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
11
else
(if i.val < 4140 then
0
else
11))
else
(if i.val < 4143 then
(if i.val < 4142 then
8
else
0)
else
(if i.val < 4144 then
8
else
24)))
else
(if i.val < 4148 then
(if i.val < 4146 then
8
else
(if i.val < 4147 then
0
else
23))
else
(if i.val < 4150 then
(if i.val < 4149 then
28
else
19)
else
(if i.val < 4151 then
23
else
34))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
22
else
(if i.val < 4154 then
23
else
28))
else
(if i.val < 4157 then
(if i.val < 4156 then
18
else
8)
else
(if i.val < 4158 then
7
else
25)))
else
(if i.val < 4162 then
(if i.val < 4160 then
8
else
(if i.val < 4161 then
30
else
14))
else
(if i.val < 4164 then
(if i.val < 4163 then
29
else
14)
else
(if i.val < 4165 then
13
else
22))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
15
else
(if i.val < 4168 then
31
else
0))
else
(if i.val < 4171 then
(if i.val < 4170 then
0
else
0)
else
(if i.val < 4172 then
8
else
16)))
else
(if i.val < 4176 then
(if i.val < 4174 then
31
else
(if i.val < 4175 then
30
else
14))
else
(if i.val < 4178 then
(if i.val < 4177 then
12
else
11)
else
(if i.val < 4179 then
4
else
22)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
1
else
(if i.val < 4182 then
30
else
2))
else
(if i.val < 4185 then
(if i.val < 4184 then
10
else
6)
else
(if i.val < 4186 then
18
else
23)))
else
(if i.val < 4190 then
(if i.val < 4188 then
13
else
(if i.val < 4189 then
23
else
5))
else
(if i.val < 4192 then
(if i.val < 4191 then
24
else
11)
else
(if i.val < 4193 then
5
else
1))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
31
else
(if i.val < 4196 then
23
else
29))
else
(if i.val < 4199 then
(if i.val < 4198 then
6
else
33)
else
(if i.val < 4200 then
23
else
16)))
else
(if i.val < 4204 then
(if i.val < 4202 then
33
else
(if i.val < 4203 then
10
else
20))
else
(if i.val < 4206 then
(if i.val < 4205 then
1
else
15)
else
(if i.val < 4207 then
23
else
32)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
32
else
(if i.val < 4210 then
32
else
35))
else
(if i.val < 4213 then
(if i.val < 4212 then
35
else
18)
else
(if i.val < 4214 then
22
else
12)))
else
(if i.val < 4218 then
(if i.val < 4216 then
13
else
(if i.val < 4217 then
24
else
29))
else
(if i.val < 4220 then
(if i.val < 4219 then
23
else
20)
else
(if i.val < 4221 then
21
else
17))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
5
else
(if i.val < 4224 then
11
else
12))
else
(if i.val < 4227 then
(if i.val < 4226 then
7
else
8)
else
(if i.val < 4228 then
35
else
8)))
else
(if i.val < 4232 then
(if i.val < 4230 then
32
else
(if i.val < 4231 then
23
else
22))
else
(if i.val < 4234 then
(if i.val < 4233 then
10
else
28)
else
(if i.val < 4235 then
4
else
35)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
26
else
(if i.val < 4238 then
28
else
30))
else
(if i.val < 4241 then
(if i.val < 4240 then
34
else
29)
else
(if i.val < 4242 then
19
else
19)))
else
(if i.val < 4246 then
(if i.val < 4244 then
1
else
(if i.val < 4245 then
18
else
14))
else
(if i.val < 4248 then
(if i.val < 4247 then
0
else
0)
else
(if i.val < 4249 then
0
else
8))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
33
else
(if i.val < 4252 then
22
else
13))
else
(if i.val < 4255 then
(if i.val < 4254 then
3
else
35)
else
(if i.val < 4256 then
34
else
0)))
else
(if i.val < 4260 then
(if i.val < 4258 then
0
else
(if i.val < 4259 then
18
else
22))
else
(if i.val < 4262 then
(if i.val < 4261 then
13
else
1)
else
(if i.val < 4263 then
26
else
29))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
11
else
(if i.val < 4266 then
18
else
23))
else
(if i.val < 4269 then
(if i.val < 4268 then
23
else
12)
else
(if i.val < 4270 then
25
else
23)))
else
(if i.val < 4274 then
(if i.val < 4272 then
10
else
(if i.val < 4273 then
33
else
17))
else
(if i.val < 4276 then
(if i.val < 4275 then
9
else
14)
else
(if i.val < 4277 then
22
else
0))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
3
else
(if i.val < 4280 then
30
else
6))
else
(if i.val < 4283 then
(if i.val < 4282 then
29
else
11)
else
(if i.val < 4284 then
13
else
14)))
else
(if i.val < 4288 then
(if i.val < 4286 then
0
else
(if i.val < 4287 then
14
else
13))
else
(if i.val < 4290 then
(if i.val < 4289 then
11
else
32)
else
(if i.val < 4291 then
15
else
30)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
20
else
(if i.val < 4294 then
17
else
32))
else
(if i.val < 4297 then
(if i.val < 4296 then
22
else
20)
else
(if i.val < 4298 then
19
else
22)))
else
(if i.val < 4302 then
(if i.val < 4300 then
31
else
(if i.val < 4301 then
0
else
1))
else
(if i.val < 4304 then
(if i.val < 4303 then
1
else
8)
else
(if i.val < 4305 then
24
else
5))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
5
else
(if i.val < 4308 then
12
else
7))
else
(if i.val < 4311 then
(if i.val < 4310 then
9
else
15)
else
(if i.val < 4312 then
0
else
33)))
else
(if i.val < 4316 then
(if i.val < 4314 then
22
else
(if i.val < 4315 then
34
else
18))
else
(if i.val < 4318 then
(if i.val < 4317 then
12
else
3)
else
(if i.val < 4319 then
26
else
32))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0000 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
0
else
0)
else
(if i.val < 3 then
0
else
0))
else
(if i.val < 6 then
(if i.val < 5 then
0
else
0)
else
(if i.val < 7 then
0
else
0)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
0
else
0)
else
(if i.val < 11 then
0
else
0))
else
(if i.val < 14 then
(if i.val < 13 then
0
else
0)
else
(if i.val < 15 then
0
else
0))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
0
else
0)
else
(if i.val < 19 then
0
else
27))
else
(if i.val < 22 then
(if i.val < 21 then
0
else
0)
else
(if i.val < 23 then
0
else
0)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
0
else
0)
else
(if i.val < 27 then
0
else
0))
else
(if i.val < 30 then
(if i.val < 29 then
0
else
0)
else
(if i.val < 31 then
0
else
0)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
0
else
0)
else
(if i.val < 35 then
0
else
0))
else
(if i.val < 38 then
(if i.val < 37 then
0
else
0)
else
(if i.val < 39 then
0
else
0)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
8
else
0)
else
(if i.val < 43 then
0
else
0))
else
(if i.val < 46 then
(if i.val < 45 then
0
else
0)
else
(if i.val < 47 then
0
else
0))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
0
else
0)
else
(if i.val < 51 then
0
else
0))
else
(if i.val < 54 then
(if i.val < 53 then
0
else
0)
else
(if i.val < 55 then
0
else
0)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
0
else
0)
else
(if i.val < 59 then
0
else
0))
else
(if i.val < 62 then
(if i.val < 61 then
9
else
0)
else
(if i.val < 63 then
10
else
0))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
0
else
0)
else
(if i.val < 67 then
0
else
0))
else
(if i.val < 70 then
(if i.val < 69 then
0
else
0)
else
(if i.val < 71 then
0
else
0)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
12
else
0)
else
(if i.val < 75 then
0
else
0))
else
(if i.val < 78 then
(if i.val < 77 then
0
else
0)
else
(if i.val < 79 then
0
else
0))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
0
else
0)
else
(if i.val < 83 then
0
else
0))
else
(if i.val < 86 then
(if i.val < 85 then
0
else
14)
else
(if i.val < 87 then
0
else
0)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
0
else
0)
else
(if i.val < 91 then
27
else
0))
else
(if i.val < 94 then
(if i.val < 93 then
0
else
0)
else
(if i.val < 95 then
0
else
0)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
35
else
29)
else
(if i.val < 99 then
0
else
0))
else
(if i.val < 102 then
(if i.val < 101 then
0
else
0)
else
(if i.val < 103 then
0
else
9)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
0
else
0)
else
(if i.val < 107 then
9
else
0))
else
(if i.val < 110 then
(if i.val < 109 then
0
else
8)
else
(if i.val < 111 then
12
else
0))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
0
else
0)
else
(if i.val < 115 then
0
else
8))
else
(if i.val < 118 then
(if i.val < 117 then
0
else
0)
else
(if i.val < 119 then
0
else
0)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
0
else
0)
else
(if i.val < 123 then
0
else
0))
else
(if i.val < 126 then
(if i.val < 125 then
0
else
0)
else
(if i.val < 127 then
0
else
0)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
0
else
0)
else
(if i.val < 131 then
0
else
0))
else
(if i.val < 134 then
(if i.val < 133 then
0
else
0)
else
(if i.val < 135 then
0
else
0)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
0
else
0)
else
(if i.val < 139 then
0
else
0))
else
(if i.val < 142 then
(if i.val < 141 then
0
else
0)
else
(if i.val < 143 then
0
else
0))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
0
else
0)
else
(if i.val < 147 then
0
else
0))
else
(if i.val < 150 then
(if i.val < 149 then
10
else
9)
else
(if i.val < 151 then
0
else
0)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
0
else
0)
else
(if i.val < 155 then
0
else
0))
else
(if i.val < 158 then
(if i.val < 157 then
0
else
0)
else
(if i.val < 159 then
0
else
0)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
0
else
0)
else
(if i.val < 163 then
0
else
12))
else
(if i.val < 166 then
(if i.val < 165 then
0
else
27)
else
(if i.val < 167 then
9
else
0)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
9
else
0)
else
(if i.val < 171 then
0
else
0))
else
(if i.val < 174 then
(if i.val < 173 then
9
else
0)
else
(if i.val < 175 then
0
else
0))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
0
else
0)
else
(if i.val < 179 then
0
else
14))
else
(if i.val < 182 then
(if i.val < 181 then
0
else
0)
else
(if i.val < 183 then
0
else
0)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
10
else
0)
else
(if i.val < 187 then
0
else
0))
else
(if i.val < 190 then
(if i.val < 189 then
10
else
0)
else
(if i.val < 191 then
0
else
29))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
0
else
0)
else
(if i.val < 195 then
0
else
0))
else
(if i.val < 198 then
(if i.val < 197 then
0
else
29)
else
(if i.val < 199 then
0
else
29)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
0
else
0)
else
(if i.val < 203 then
0
else
12))
else
(if i.val < 206 then
(if i.val < 205 then
0
else
0)
else
(if i.val < 207 then
0
else
0))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
0
else
0)
else
(if i.val < 211 then
0
else
0))
else
(if i.val < 214 then
(if i.val < 213 then
0
else
0)
else
(if i.val < 215 then
0
else
0)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
0
else
0)
else
(if i.val < 219 then
0
else
0))
else
(if i.val < 222 then
(if i.val < 221 then
0
else
0)
else
(if i.val < 223 then
0
else
0)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
0
else
23)
else
(if i.val < 227 then
0
else
0))
else
(if i.val < 230 then
(if i.val < 229 then
0
else
0)
else
(if i.val < 231 then
14
else
0)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
0
else
0)
else
(if i.val < 235 then
0
else
0))
else
(if i.val < 238 then
(if i.val < 237 then
0
else
0)
else
(if i.val < 239 then
0
else
0))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
0
else
0)
else
(if i.val < 243 then
28
else
0))
else
(if i.val < 246 then
(if i.val < 245 then
0
else
0)
else
(if i.val < 247 then
0
else
0)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
0
else
0)
else
(if i.val < 251 then
14
else
27))
else
(if i.val < 254 then
(if i.val < 253 then
0
else
0)
else
(if i.val < 255 then
0
else
0))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
10
else
0)
else
(if i.val < 259 then
0
else
0))
else
(if i.val < 262 then
(if i.val < 261 then
0
else
0)
else
(if i.val < 263 then
0
else
23)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
16
else
14)
else
(if i.val < 267 then
0
else
0))
else
(if i.val < 270 then
(if i.val < 269 then
9
else
0)
else
(if i.val < 271 then
27
else
0))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
0
else
0)
else
(if i.val < 275 then
0
else
35))
else
(if i.val < 278 then
(if i.val < 277 then
0
else
0)
else
(if i.val < 279 then
0
else
0)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
9
else
0)
else
(if i.val < 283 then
0
else
8))
else
(if i.val < 286 then
(if i.val < 285 then
0
else
0)
else
(if i.val < 287 then
0
else
0)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
10
else
0)
else
(if i.val < 291 then
0
else
0))
else
(if i.val < 294 then
(if i.val < 293 then
11
else
0)
else
(if i.val < 295 then
35
else
9)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
0
else
0)
else
(if i.val < 299 then
8
else
0))
else
(if i.val < 302 then
(if i.val < 301 then
0
else
0)
else
(if i.val < 303 then
0
else
0))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
0
else
0)
else
(if i.val < 307 then
0
else
35))
else
(if i.val < 310 then
(if i.val < 309 then
8
else
0)
else
(if i.val < 311 then
0
else
0)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
0
else
9)
else
(if i.val < 315 then
0
else
0))
else
(if i.val < 318 then
(if i.val < 317 then
0
else
0)
else
(if i.val < 319 then
0
else
0))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
0
else
0)
else
(if i.val < 323 then
0
else
0))
else
(if i.val < 326 then
(if i.val < 325 then
0
else
0)
else
(if i.val < 327 then
0
else
0)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
0
else
0)
else
(if i.val < 331 then
0
else
0))
else
(if i.val < 334 then
(if i.val < 333 then
0
else
0)
else
(if i.val < 335 then
0
else
0))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
0
else
0)
else
(if i.val < 339 then
0
else
6))
else
(if i.val < 342 then
(if i.val < 341 then
8
else
0)
else
(if i.val < 343 then
25
else
0)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
0
else
0)
else
(if i.val < 347 then
0
else
0))
else
(if i.val < 350 then
(if i.val < 349 then
0
else
0)
else
(if i.val < 351 then
0
else
0)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
0
else
0)
else
(if i.val < 355 then
0
else
0))
else
(if i.val < 358 then
(if i.val < 357 then
0
else
0)
else
(if i.val < 359 then
0
else
0)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
14
else
0)
else
(if i.val < 363 then
0
else
0))
else
(if i.val < 366 then
(if i.val < 365 then
0
else
0)
else
(if i.val < 367 then
0
else
0))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
0
else
0)
else
(if i.val < 371 then
0
else
0))
else
(if i.val < 374 then
(if i.val < 373 then
11
else
0)
else
(if i.val < 375 then
0
else
0)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
0
else
0)
else
(if i.val < 379 then
0
else
8))
else
(if i.val < 382 then
(if i.val < 381 then
0
else
0)
else
(if i.val < 383 then
13
else
0)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
0
else
0)
else
(if i.val < 387 then
0
else
0))
else
(if i.val < 390 then
(if i.val < 389 then
0
else
0)
else
(if i.val < 391 then
0
else
0)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
0
else
0)
else
(if i.val < 395 then
0
else
0))
else
(if i.val < 398 then
(if i.val < 397 then
0
else
0)
else
(if i.val < 399 then
0
else
0))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
0
else
0)
else
(if i.val < 403 then
0
else
0))
else
(if i.val < 406 then
(if i.val < 405 then
12
else
0)
else
(if i.val < 407 then
29
else
0)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
9
else
0)
else
(if i.val < 411 then
0
else
0))
else
(if i.val < 414 then
(if i.val < 413 then
12
else
10)
else
(if i.val < 415 then
9
else
0)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
0
else
0)
else
(if i.val < 419 then
0
else
0))
else
(if i.val < 422 then
(if i.val < 421 then
0
else
12)
else
(if i.val < 423 then
10
else
9)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
0
else
0)
else
(if i.val < 427 then
0
else
0))
else
(if i.val < 430 then
(if i.val < 429 then
25
else
25)
else
(if i.val < 431 then
8
else
9))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
9
else
8)
else
(if i.val < 435 then
0
else
0))
else
(if i.val < 438 then
(if i.val < 437 then
14
else
0)
else
(if i.val < 439 then
0
else
0)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
0
else
0)
else
(if i.val < 443 then
0
else
10))
else
(if i.val < 446 then
(if i.val < 445 then
0
else
0)
else
(if i.val < 447 then
0
else
9))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
0
else
0)
else
(if i.val < 451 then
0
else
0))
else
(if i.val < 454 then
(if i.val < 453 then
0
else
0)
else
(if i.val < 455 then
0
else
32)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
27
else
0)
else
(if i.val < 459 then
0
else
0))
else
(if i.val < 462 then
(if i.val < 461 then
0
else
27)
else
(if i.val < 463 then
0
else
14))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
0
else
0)
else
(if i.val < 467 then
0
else
0))
else
(if i.val < 470 then
(if i.val < 469 then
23
else
0)
else
(if i.val < 471 then
14
else
0)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
0
else
0)
else
(if i.val < 475 then
0
else
27))
else
(if i.val < 478 then
(if i.val < 477 then
0
else
0)
else
(if i.val < 479 then
14
else
0)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
0
else
0)
else
(if i.val < 483 then
0
else
0))
else
(if i.val < 486 then
(if i.val < 485 then
0
else
0)
else
(if i.val < 487 then
0
else
0)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
0
else
0)
else
(if i.val < 491 then
0
else
25))
else
(if i.val < 494 then
(if i.val < 493 then
12
else
0)
else
(if i.val < 495 then
0
else
0))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
0
else
0)
else
(if i.val < 499 then
9
else
0))
else
(if i.val < 502 then
(if i.val < 501 then
0
else
0)
else
(if i.val < 503 then
0
else
0)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
0
else
14)
else
(if i.val < 507 then
0
else
0))
else
(if i.val < 510 then
(if i.val < 509 then
0
else
0)
else
(if i.val < 511 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0001 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
0
else
0)
else
(if i.val < 515 then
0
else
0))
else
(if i.val < 518 then
(if i.val < 517 then
0
else
0)
else
(if i.val < 519 then
0
else
0)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
0
else
28)
else
(if i.val < 523 then
0
else
0))
else
(if i.val < 526 then
(if i.val < 525 then
0
else
0)
else
(if i.val < 527 then
0
else
0))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
23
else
24)
else
(if i.val < 531 then
0
else
0))
else
(if i.val < 534 then
(if i.val < 533 then
0
else
0)
else
(if i.val < 535 then
9
else
9)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
23
else
23)
else
(if i.val < 539 then
23
else
0))
else
(if i.val < 542 then
(if i.val < 541 then
25
else
0)
else
(if i.val < 543 then
0
else
0)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
14
else
14)
else
(if i.val < 547 then
0
else
0))
else
(if i.val < 550 then
(if i.val < 549 then
0
else
0)
else
(if i.val < 551 then
0
else
0)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
0
else
25)
else
(if i.val < 555 then
23
else
0))
else
(if i.val < 558 then
(if i.val < 557 then
0
else
0)
else
(if i.val < 559 then
23
else
0))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
0
else
0)
else
(if i.val < 563 then
0
else
0))
else
(if i.val < 566 then
(if i.val < 565 then
0
else
14)
else
(if i.val < 567 then
0
else
0)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
0
else
0)
else
(if i.val < 571 then
0
else
0))
else
(if i.val < 574 then
(if i.val < 573 then
0
else
0)
else
(if i.val < 575 then
10
else
0))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
0
else
0)
else
(if i.val < 579 then
0
else
0))
else
(if i.val < 582 then
(if i.val < 581 then
0
else
0)
else
(if i.val < 583 then
0
else
0)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
0
else
0)
else
(if i.val < 587 then
0
else
14))
else
(if i.val < 590 then
(if i.val < 589 then
0
else
0)
else
(if i.val < 591 then
0
else
0))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
0
else
0)
else
(if i.val < 595 then
0
else
0))
else
(if i.val < 598 then
(if i.val < 597 then
0
else
0)
else
(if i.val < 599 then
0
else
0)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
0
else
25)
else
(if i.val < 603 then
26
else
0))
else
(if i.val < 606 then
(if i.val < 605 then
29
else
0)
else
(if i.val < 607 then
0
else
0)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
0
else
0)
else
(if i.val < 611 then
0
else
8))
else
(if i.val < 614 then
(if i.val < 613 then
23
else
35)
else
(if i.val < 615 then
0
else
23)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
23
else
0)
else
(if i.val < 619 then
0
else
0))
else
(if i.val < 622 then
(if i.val < 621 then
14
else
0)
else
(if i.val < 623 then
33
else
25))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
23
else
0)
else
(if i.val < 627 then
23
else
0))
else
(if i.val < 630 then
(if i.val < 629 then
0
else
0)
else
(if i.val < 631 then
0
else
0)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
0
else
14)
else
(if i.val < 635 then
0
else
0))
else
(if i.val < 638 then
(if i.val < 637 then
0
else
0)
else
(if i.val < 639 then
14
else
29)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
0
else
0)
else
(if i.val < 643 then
0
else
0))
else
(if i.val < 646 then
(if i.val < 645 then
0
else
0)
else
(if i.val < 647 then
0
else
23)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
0
else
0)
else
(if i.val < 651 then
9
else
0))
else
(if i.val < 654 then
(if i.val < 653 then
0
else
0)
else
(if i.val < 655 then
0
else
9))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
35
else
9)
else
(if i.val < 659 then
0
else
0))
else
(if i.val < 662 then
(if i.val < 661 then
8
else
0)
else
(if i.val < 663 then
0
else
0)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
0
else
0)
else
(if i.val < 667 then
0
else
25))
else
(if i.val < 670 then
(if i.val < 669 then
0
else
35)
else
(if i.val < 671 then
8
else
0)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
0
else
0)
else
(if i.val < 675 then
0
else
0))
else
(if i.val < 678 then
(if i.val < 677 then
0
else
11)
else
(if i.val < 679 then
0
else
8)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
8
else
11)
else
(if i.val < 683 then
11
else
0))
else
(if i.val < 686 then
(if i.val < 685 then
0
else
0)
else
(if i.val < 687 then
0
else
0))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
0
else
6)
else
(if i.val < 691 then
35
else
22))
else
(if i.val < 694 then
(if i.val < 693 then
0
else
0)
else
(if i.val < 695 then
8
else
0)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
35
else
35)
else
(if i.val < 699 then
8
else
0))
else
(if i.val < 702 then
(if i.val < 701 then
25
else
0)
else
(if i.val < 703 then
18
else
0))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
0
else
0)
else
(if i.val < 707 then
0
else
0))
else
(if i.val < 710 then
(if i.val < 709 then
0
else
0)
else
(if i.val < 711 then
0
else
0)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
0
else
8)
else
(if i.val < 715 then
0
else
0))
else
(if i.val < 718 then
(if i.val < 717 then
14
else
0)
else
(if i.val < 719 then
0
else
0))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
35
else
0)
else
(if i.val < 723 then
0
else
0))
else
(if i.val < 726 then
(if i.val < 725 then
0
else
0)
else
(if i.val < 727 then
0
else
11)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
0
else
0)
else
(if i.val < 731 then
9
else
0))
else
(if i.val < 734 then
(if i.val < 733 then
0
else
0)
else
(if i.val < 735 then
8
else
0)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
0
else
0)
else
(if i.val < 739 then
18
else
0))
else
(if i.val < 742 then
(if i.val < 741 then
0
else
0)
else
(if i.val < 743 then
0
else
0)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
0
else
0)
else
(if i.val < 747 then
0
else
0))
else
(if i.val < 750 then
(if i.val < 749 then
0
else
25)
else
(if i.val < 751 then
0
else
0))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
0
else
0)
else
(if i.val < 755 then
0
else
0))
else
(if i.val < 758 then
(if i.val < 757 then
0
else
8)
else
(if i.val < 759 then
0
else
0)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
0
else
0)
else
(if i.val < 763 then
0
else
0))
else
(if i.val < 766 then
(if i.val < 765 then
0
else
0)
else
(if i.val < 767 then
8
else
22))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
0
else
8)
else
(if i.val < 771 then
0
else
0))
else
(if i.val < 774 then
(if i.val < 773 then
0
else
8)
else
(if i.val < 775 then
8
else
0)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
0
else
6)
else
(if i.val < 779 then
8
else
8))
else
(if i.val < 782 then
(if i.val < 781 then
0
else
0)
else
(if i.val < 783 then
0
else
0))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
0
else
0)
else
(if i.val < 787 then
0
else
0))
else
(if i.val < 790 then
(if i.val < 789 then
0
else
0)
else
(if i.val < 791 then
0
else
0)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
0
else
0)
else
(if i.val < 795 then
0
else
0))
else
(if i.val < 798 then
(if i.val < 797 then
0
else
14)
else
(if i.val < 799 then
31
else
0)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
0
else
0)
else
(if i.val < 803 then
0
else
16))
else
(if i.val < 806 then
(if i.val < 805 then
31
else
14)
else
(if i.val < 807 then
0
else
0)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
0
else
14)
else
(if i.val < 811 then
24
else
0))
else
(if i.val < 814 then
(if i.val < 813 then
0
else
0)
else
(if i.val < 815 then
0
else
0))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
0
else
0)
else
(if i.val < 819 then
0
else
0))
else
(if i.val < 822 then
(if i.val < 821 then
0
else
14)
else
(if i.val < 823 then
0
else
0)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
0
else
0)
else
(if i.val < 827 then
0
else
0))
else
(if i.val < 830 then
(if i.val < 829 then
0
else
0)
else
(if i.val < 831 then
0
else
14))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
0
else
0)
else
(if i.val < 835 then
0
else
8))
else
(if i.val < 838 then
(if i.val < 837 then
0
else
11)
else
(if i.val < 839 then
8
else
10)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
8
else
0)
else
(if i.val < 843 then
0
else
11))
else
(if i.val < 846 then
(if i.val < 845 then
0
else
0)
else
(if i.val < 847 then
0
else
11))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
0
else
0)
else
(if i.val < 851 then
11
else
0))
else
(if i.val < 854 then
(if i.val < 853 then
0
else
0)
else
(if i.val < 855 then
0
else
0)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
0
else
0)
else
(if i.val < 859 then
0
else
0))
else
(if i.val < 862 then
(if i.val < 861 then
0
else
0)
else
(if i.val < 863 then
0
else
28)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
0
else
13)
else
(if i.val < 867 then
28
else
14))
else
(if i.val < 870 then
(if i.val < 869 then
31
else
0)
else
(if i.val < 871 then
0
else
0)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
0
else
0)
else
(if i.val < 875 then
11
else
18))
else
(if i.val < 878 then
(if i.val < 877 then
14
else
0)
else
(if i.val < 879 then
11
else
31))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
0
else
11)
else
(if i.val < 883 then
13
else
0))
else
(if i.val < 886 then
(if i.val < 885 then
0
else
0)
else
(if i.val < 887 then
0
else
0)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
0
else
0)
else
(if i.val < 891 then
0
else
0))
else
(if i.val < 894 then
(if i.val < 893 then
0
else
0)
else
(if i.val < 895 then
0
else
0)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
0
else
0)
else
(if i.val < 899 then
0
else
0))
else
(if i.val < 902 then
(if i.val < 901 then
0
else
14)
else
(if i.val < 903 then
29
else
29)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
0
else
0)
else
(if i.val < 907 then
23
else
0))
else
(if i.val < 910 then
(if i.val < 909 then
0
else
0)
else
(if i.val < 911 then
0
else
25))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
12
else
0)
else
(if i.val < 915 then
0
else
14))
else
(if i.val < 918 then
(if i.val < 917 then
29
else
0)
else
(if i.val < 919 then
0
else
0)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
0
else
10)
else
(if i.val < 923 then
8
else
0))
else
(if i.val < 926 then
(if i.val < 925 then
0
else
0)
else
(if i.val < 927 then
14
else
0)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
9
else
10)
else
(if i.val < 931 then
32
else
27))
else
(if i.val < 934 then
(if i.val < 933 then
9
else
0)
else
(if i.val < 935 then
17
else
0)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
12
else
0)
else
(if i.val < 939 then
9
else
0))
else
(if i.val < 942 then
(if i.val < 941 then
31
else
10)
else
(if i.val < 943 then
0
else
0))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
28
else
0)
else
(if i.val < 947 then
0
else
10))
else
(if i.val < 950 then
(if i.val < 949 then
9
else
31)
else
(if i.val < 951 then
14
else
32)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
0
else
0)
else
(if i.val < 955 then
10
else
9))
else
(if i.val < 958 then
(if i.val < 957 then
25
else
8)
else
(if i.val < 959 then
0
else
9))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
0
else
6)
else
(if i.val < 963 then
35
else
0))
else
(if i.val < 966 then
(if i.val < 965 then
26
else
25)
else
(if i.val < 967 then
0
else
14)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
14
else
10)
else
(if i.val < 971 then
0
else
0))
else
(if i.val < 974 then
(if i.val < 973 then
0
else
0)
else
(if i.val < 975 then
9
else
25))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
0
else
14)
else
(if i.val < 979 then
0
else
0))
else
(if i.val < 982 then
(if i.val < 981 then
0
else
0)
else
(if i.val < 983 then
0
else
10)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
0
else
0)
else
(if i.val < 987 then
14
else
0))
else
(if i.val < 990 then
(if i.val < 989 then
0
else
0)
else
(if i.val < 991 then
0
else
0)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
10
else
0)
else
(if i.val < 995 then
0
else
8))
else
(if i.val < 998 then
(if i.val < 997 then
0
else
0)
else
(if i.val < 999 then
0
else
0)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
0
else
0)
else
(if i.val < 1003 then
9
else
0))
else
(if i.val < 1006 then
(if i.val < 1005 then
0
else
0)
else
(if i.val < 1007 then
0
else
14))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
0
else
10)
else
(if i.val < 1011 then
0
else
11))
else
(if i.val < 1014 then
(if i.val < 1013 then
0
else
8)
else
(if i.val < 1015 then
13
else
0)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
0
else
0)
else
(if i.val < 1019 then
0
else
0))
else
(if i.val < 1022 then
(if i.val < 1021 then
0
else
23)
else
(if i.val < 1023 then
0
else
29)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0002 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
0
else
0)
else
(if i.val < 1027 then
0
else
14))
else
(if i.val < 1030 then
(if i.val < 1029 then
0
else
0)
else
(if i.val < 1031 then
9
else
0)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
0
else
23)
else
(if i.val < 1035 then
23
else
14))
else
(if i.val < 1038 then
(if i.val < 1037 then
14
else
0)
else
(if i.val < 1039 then
14
else
0))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
18
else
0)
else
(if i.val < 1043 then
0
else
29))
else
(if i.val < 1046 then
(if i.val < 1045 then
23
else
0)
else
(if i.val < 1047 then
0
else
0)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
0
else
14)
else
(if i.val < 1051 then
0
else
0))
else
(if i.val < 1054 then
(if i.val < 1053 then
14
else
29)
else
(if i.val < 1055 then
14
else
0)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
14
else
25)
else
(if i.val < 1059 then
10
else
9))
else
(if i.val < 1062 then
(if i.val < 1061 then
29
else
29)
else
(if i.val < 1063 then
8
else
0)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
0
else
0)
else
(if i.val < 1067 then
1
else
9))
else
(if i.val < 1070 then
(if i.val < 1069 then
14
else
0)
else
(if i.val < 1071 then
0
else
0))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
0
else
0)
else
(if i.val < 1075 then
14
else
0))
else
(if i.val < 1078 then
(if i.val < 1077 then
31
else
0)
else
(if i.val < 1079 then
25
else
28)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
27
else
0)
else
(if i.val < 1083 then
0
else
0))
else
(if i.val < 1086 then
(if i.val < 1085 then
0
else
0)
else
(if i.val < 1087 then
0
else
0))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
0
else
0)
else
(if i.val < 1091 then
0
else
0))
else
(if i.val < 1094 then
(if i.val < 1093 then
0
else
12)
else
(if i.val < 1095 then
0
else
0)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
8
else
9)
else
(if i.val < 1099 then
14
else
0))
else
(if i.val < 1102 then
(if i.val < 1101 then
0
else
0)
else
(if i.val < 1103 then
0
else
0))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
0
else
0)
else
(if i.val < 1107 then
23
else
0))
else
(if i.val < 1110 then
(if i.val < 1109 then
0
else
14)
else
(if i.val < 1111 then
14
else
32)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
0
else
0)
else
(if i.val < 1115 then
1
else
0))
else
(if i.val < 1118 then
(if i.val < 1117 then
0
else
0)
else
(if i.val < 1119 then
0
else
0)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
0
else
0)
else
(if i.val < 1123 then
0
else
0))
else
(if i.val < 1126 then
(if i.val < 1125 then
0
else
0)
else
(if i.val < 1127 then
24
else
0)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
0
else
33)
else
(if i.val < 1131 then
0
else
0))
else
(if i.val < 1134 then
(if i.val < 1133 then
0
else
14)
else
(if i.val < 1135 then
0
else
0))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
0
else
0)
else
(if i.val < 1139 then
0
else
14))
else
(if i.val < 1142 then
(if i.val < 1141 then
0
else
0)
else
(if i.val < 1143 then
23
else
0)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
23
else
0)
else
(if i.val < 1147 then
0
else
28))
else
(if i.val < 1150 then
(if i.val < 1149 then
5
else
0)
else
(if i.val < 1151 then
0
else
23)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
23
else
24)
else
(if i.val < 1155 then
17
else
0))
else
(if i.val < 1158 then
(if i.val < 1157 then
25
else
0)
else
(if i.val < 1159 then
3
else
0)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
0
else
0)
else
(if i.val < 1163 then
23
else
0))
else
(if i.val < 1166 then
(if i.val < 1165 then
0
else
25)
else
(if i.val < 1167 then
23
else
23))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
23
else
0)
else
(if i.val < 1171 then
0
else
0))
else
(if i.val < 1174 then
(if i.val < 1173 then
0
else
14)
else
(if i.val < 1175 then
17
else
0)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
0
else
14)
else
(if i.val < 1179 then
14
else
19))
else
(if i.val < 1182 then
(if i.val < 1181 then
16
else
0)
else
(if i.val < 1183 then
10
else
31)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
14
else
0)
else
(if i.val < 1187 then
0
else
0))
else
(if i.val < 1190 then
(if i.val < 1189 then
0
else
9)
else
(if i.val < 1191 then
0
else
0)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
1
else
0)
else
(if i.val < 1195 then
0
else
0))
else
(if i.val < 1198 then
(if i.val < 1197 then
0
else
0)
else
(if i.val < 1199 then
25
else
14))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
25
else
23)
else
(if i.val < 1203 then
8
else
23))
else
(if i.val < 1206 then
(if i.val < 1205 then
25
else
0)
else
(if i.val < 1207 then
0
else
0)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
23
else
23)
else
(if i.val < 1211 then
9
else
23))
else
(if i.val < 1214 then
(if i.val < 1213 then
29
else
0)
else
(if i.val < 1215 then
24
else
25))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
0
else
14)
else
(if i.val < 1219 then
24
else
0))
else
(if i.val < 1222 then
(if i.val < 1221 then
0
else
0)
else
(if i.val < 1223 then
0
else
0)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
0
else
0)
else
(if i.val < 1227 then
0
else
0))
else
(if i.val < 1230 then
(if i.val < 1229 then
0
else
0)
else
(if i.val < 1231 then
0
else
0))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
0
else
0)
else
(if i.val < 1235 then
0
else
0))
else
(if i.val < 1238 then
(if i.val < 1237 then
0
else
0)
else
(if i.val < 1239 then
9
else
0)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
10
else
10)
else
(if i.val < 1243 then
10
else
0))
else
(if i.val < 1246 then
(if i.val < 1245 then
0
else
25)
else
(if i.val < 1247 then
25
else
8)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
9
else
8)
else
(if i.val < 1251 then
0
else
11))
else
(if i.val < 1254 then
(if i.val < 1253 then
0
else
11)
else
(if i.val < 1255 then
10
else
0)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
0
else
24)
else
(if i.val < 1259 then
0
else
27))
else
(if i.val < 1262 then
(if i.val < 1261 then
0
else
0)
else
(if i.val < 1263 then
0
else
0))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
0
else
28)
else
(if i.val < 1267 then
14
else
14))
else
(if i.val < 1270 then
(if i.val < 1269 then
0
else
0)
else
(if i.val < 1271 then
0
else
0)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
0
else
0)
else
(if i.val < 1275 then
0
else
10))
else
(if i.val < 1278 then
(if i.val < 1277 then
0
else
0)
else
(if i.val < 1279 then
0
else
0))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
0
else
0)
else
(if i.val < 1283 then
9
else
0))
else
(if i.val < 1286 then
(if i.val < 1285 then
0
else
32)
else
(if i.val < 1287 then
0
else
0)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
9
else
25)
else
(if i.val < 1291 then
30
else
35))
else
(if i.val < 1294 then
(if i.val < 1293 then
25
else
25)
else
(if i.val < 1295 then
33
else
9))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
26
else
8)
else
(if i.val < 1299 then
22
else
3))
else
(if i.val < 1302 then
(if i.val < 1301 then
0
else
29)
else
(if i.val < 1303 then
23
else
0)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
0
else
0)
else
(if i.val < 1307 then
0
else
0))
else
(if i.val < 1310 then
(if i.val < 1309 then
0
else
0)
else
(if i.val < 1311 then
0
else
0)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
0
else
0)
else
(if i.val < 1315 then
32
else
0))
else
(if i.val < 1318 then
(if i.val < 1317 then
0
else
0)
else
(if i.val < 1319 then
23
else
23)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
0
else
27)
else
(if i.val < 1323 then
0
else
23))
else
(if i.val < 1326 then
(if i.val < 1325 then
23
else
23)
else
(if i.val < 1327 then
23
else
0))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
18
else
29)
else
(if i.val < 1331 then
28
else
14))
else
(if i.val < 1334 then
(if i.val < 1333 then
0
else
23)
else
(if i.val < 1335 then
0
else
21)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
0
else
0)
else
(if i.val < 1339 then
8
else
25))
else
(if i.val < 1342 then
(if i.val < 1341 then
23
else
0)
else
(if i.val < 1343 then
0
else
29))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
23
else
23)
else
(if i.val < 1347 then
29
else
0))
else
(if i.val < 1350 then
(if i.val < 1349 then
0
else
14)
else
(if i.val < 1351 then
0
else
0)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
0
else
0)
else
(if i.val < 1355 then
0
else
28))
else
(if i.val < 1358 then
(if i.val < 1357 then
10
else
0)
else
(if i.val < 1359 then
0
else
0))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
0
else
0)
else
(if i.val < 1363 then
0
else
0))
else
(if i.val < 1366 then
(if i.val < 1365 then
18
else
0)
else
(if i.val < 1367 then
0
else
29)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
0
else
14)
else
(if i.val < 1371 then
29
else
0))
else
(if i.val < 1374 then
(if i.val < 1373 then
0
else
0)
else
(if i.val < 1375 then
25
else
26)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
29
else
0)
else
(if i.val < 1379 then
0
else
8))
else
(if i.val < 1382 then
(if i.val < 1381 then
23
else
35)
else
(if i.val < 1383 then
0
else
23)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
29
else
0)
else
(if i.val < 1387 then
33
else
25))
else
(if i.val < 1390 then
(if i.val < 1389 then
23
else
0)
else
(if i.val < 1391 then
23
else
9))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
21
else
0)
else
(if i.val < 1395 then
0
else
29))
else
(if i.val < 1398 then
(if i.val < 1397 then
0
else
14)
else
(if i.val < 1399 then
0
else
8)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
0
else
0)
else
(if i.val < 1403 then
14
else
35))
else
(if i.val < 1406 then
(if i.val < 1405 then
0
else
0)
else
(if i.val < 1407 then
0
else
6)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
35
else
0)
else
(if i.val < 1411 then
0
else
0))
else
(if i.val < 1414 then
(if i.val < 1413 then
35
else
35)
else
(if i.val < 1415 then
8
else
0)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
18
else
0)
else
(if i.val < 1419 then
0
else
6))
else
(if i.val < 1422 then
(if i.val < 1421 then
14
else
0)
else
(if i.val < 1423 then
18
else
28))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
0
else
8)
else
(if i.val < 1427 then
0
else
14))
else
(if i.val < 1430 then
(if i.val < 1429 then
0
else
0)
else
(if i.val < 1431 then
0
else
0)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
10
else
11)
else
(if i.val < 1435 then
11
else
11))
else
(if i.val < 1438 then
(if i.val < 1437 then
9
else
0)
else
(if i.val < 1439 then
0
else
8)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
18
else
18)
else
(if i.val < 1443 then
11
else
11))
else
(if i.val < 1446 then
(if i.val < 1445 then
11
else
11)
else
(if i.val < 1447 then
0
else
0)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
0
else
25)
else
(if i.val < 1451 then
26
else
0))
else
(if i.val < 1454 then
(if i.val < 1453 then
25
else
23)
else
(if i.val < 1455 then
0
else
0))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
8
else
0)
else
(if i.val < 1459 then
0
else
22))
else
(if i.val < 1462 then
(if i.val < 1461 then
6
else
22)
else
(if i.val < 1463 then
0
else
35)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
8
else
0)
else
(if i.val < 1467 then
22
else
8))
else
(if i.val < 1470 then
(if i.val < 1469 then
0
else
6)
else
(if i.val < 1471 then
8
else
8))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
27
else
35)
else
(if i.val < 1475 then
8
else
0))
else
(if i.val < 1478 then
(if i.val < 1477 then
0
else
33)
else
(if i.val < 1479 then
21
else
18)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
0
else
0)
else
(if i.val < 1483 then
22
else
34))
else
(if i.val < 1486 then
(if i.val < 1485 then
0
else
0)
else
(if i.val < 1487 then
24
else
0))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
0
else
21)
else
(if i.val < 1491 then
31
else
0))
else
(if i.val < 1494 then
(if i.val < 1493 then
0
else
0)
else
(if i.val < 1495 then
0
else
0)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
31
else
14)
else
(if i.val < 1499 then
0
else
0))
else
(if i.val < 1502 then
(if i.val < 1501 then
14
else
0)
else
(if i.val < 1503 then
21
else
0)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
0
else
0)
else
(if i.val < 1507 then
14
else
0))
else
(if i.val < 1510 then
(if i.val < 1509 then
0
else
0)
else
(if i.val < 1511 then
0
else
21)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
0
else
0)
else
(if i.val < 1515 then
14
else
0))
else
(if i.val < 1518 then
(if i.val < 1517 then
0
else
8)
else
(if i.val < 1519 then
0
else
11))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
8
else
10)
else
(if i.val < 1523 then
8
else
11))
else
(if i.val < 1526 then
(if i.val < 1525 then
10
else
0)
else
(if i.val < 1527 then
25
else
11)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
35
else
0)
else
(if i.val < 1531 then
11
else
9))
else
(if i.val < 1534 then
(if i.val < 1533 then
8
else
0)
else
(if i.val < 1535 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0003 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
9
else
0)
else
(if i.val < 1539 then
13
else
28))
else
(if i.val < 1542 then
(if i.val < 1541 then
14
else
0)
else
(if i.val < 1543 then
0
else
0)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
21
else
0)
else
(if i.val < 1547 then
11
else
0))
else
(if i.val < 1550 then
(if i.val < 1549 then
11
else
13)
else
(if i.val < 1551 then
0
else
0))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
0
else
0)
else
(if i.val < 1555 then
0
else
0))
else
(if i.val < 1558 then
(if i.val < 1557 then
0
else
0)
else
(if i.val < 1559 then
0
else
0)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
0
else
0)
else
(if i.val < 1563 then
7
else
25))
else
(if i.val < 1566 then
(if i.val < 1565 then
0
else
0)
else
(if i.val < 1567 then
8
else
0)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
0
else
0)
else
(if i.val < 1571 then
0
else
0))
else
(if i.val < 1574 then
(if i.val < 1573 then
0
else
0)
else
(if i.val < 1575 then
8
else
24)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
0
else
0)
else
(if i.val < 1579 then
22
else
24))
else
(if i.val < 1582 then
(if i.val < 1581 then
14
else
0)
else
(if i.val < 1583 then
0
else
0))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
0
else
0)
else
(if i.val < 1587 then
0
else
8))
else
(if i.val < 1590 then
(if i.val < 1589 then
21
else
0)
else
(if i.val < 1591 then
6
else
25)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
21
else
25)
else
(if i.val < 1595 then
0
else
5))
else
(if i.val < 1598 then
(if i.val < 1597 then
22
else
8)
else
(if i.val < 1599 then
0
else
0))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
22
else
25)
else
(if i.val < 1603 then
35
else
25))
else
(if i.val < 1606 then
(if i.val < 1605 then
0
else
8)
else
(if i.val < 1607 then
0
else
0)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
0
else
6)
else
(if i.val < 1611 then
6
else
8))
else
(if i.val < 1614 then
(if i.val < 1613 then
8
else
0)
else
(if i.val < 1615 then
0
else
0))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
21
else
0)
else
(if i.val < 1619 then
0
else
0))
else
(if i.val < 1622 then
(if i.val < 1621 then
0
else
18)
else
(if i.val < 1623 then
18
else
0)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
0
else
33)
else
(if i.val < 1627 then
0
else
8))
else
(if i.val < 1630 then
(if i.val < 1629 then
0
else
0)
else
(if i.val < 1631 then
33
else
0)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
0
else
0)
else
(if i.val < 1635 then
14
else
0))
else
(if i.val < 1638 then
(if i.val < 1637 then
14
else
0)
else
(if i.val < 1639 then
0
else
0)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
14
else
0)
else
(if i.val < 1643 then
14
else
31))
else
(if i.val < 1646 then
(if i.val < 1645 then
0
else
0)
else
(if i.val < 1647 then
0
else
11))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
0
else
18)
else
(if i.val < 1651 then
6
else
0))
else
(if i.val < 1654 then
(if i.val < 1653 then
0
else
9)
else
(if i.val < 1655 then
0
else
11)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
25
else
0)
else
(if i.val < 1659 then
0
else
17))
else
(if i.val < 1662 then
(if i.val < 1661 then
0
else
0)
else
(if i.val < 1663 then
8
else
0)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
0
else
0)
else
(if i.val < 1667 then
0
else
0))
else
(if i.val < 1670 then
(if i.val < 1669 then
0
else
14)
else
(if i.val < 1671 then
14
else
0)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
0
else
0)
else
(if i.val < 1675 then
0
else
0))
else
(if i.val < 1678 then
(if i.val < 1677 then
0
else
0)
else
(if i.val < 1679 then
0
else
33))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
0
else
14)
else
(if i.val < 1683 then
0
else
0))
else
(if i.val < 1686 then
(if i.val < 1685 then
0
else
0)
else
(if i.val < 1687 then
0
else
25)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
1
else
14)
else
(if i.val < 1691 then
0
else
14))
else
(if i.val < 1694 then
(if i.val < 1693 then
14
else
0)
else
(if i.val < 1695 then
0
else
0)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
33
else
0)
else
(if i.val < 1699 then
14
else
0))
else
(if i.val < 1702 then
(if i.val < 1701 then
8
else
11)
else
(if i.val < 1703 then
25
else
10)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
8
else
11)
else
(if i.val < 1707 then
11
else
0))
else
(if i.val < 1710 then
(if i.val < 1709 then
27
else
10)
else
(if i.val < 1711 then
11
else
0))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
11
else
11)
else
(if i.val < 1715 then
11
else
0))
else
(if i.val < 1718 then
(if i.val < 1717 then
0
else
8)
else
(if i.val < 1719 then
10
else
11)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
0
else
11)
else
(if i.val < 1723 then
0
else
0))
else
(if i.val < 1726 then
(if i.val < 1725 then
10
else
8)
else
(if i.val < 1727 then
11
else
11))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
0
else
0)
else
(if i.val < 1731 then
0
else
17))
else
(if i.val < 1734 then
(if i.val < 1733 then
0
else
14)
else
(if i.val < 1735 then
31
else
0)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
28
else
0)
else
(if i.val < 1739 then
0
else
0))
else
(if i.val < 1742 then
(if i.val < 1741 then
0
else
10)
else
(if i.val < 1743 then
0
else
0))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
18
else
25)
else
(if i.val < 1747 then
0
else
26))
else
(if i.val < 1750 then
(if i.val < 1749 then
13
else
13)
else
(if i.val < 1751 then
0
else
30)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
10
else
0)
else
(if i.val < 1755 then
0
else
8))
else
(if i.val < 1758 then
(if i.val < 1757 then
0
else
8)
else
(if i.val < 1759 then
0
else
11)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
16
else
14)
else
(if i.val < 1763 then
14
else
0))
else
(if i.val < 1766 then
(if i.val < 1765 then
18
else
0)
else
(if i.val < 1767 then
11
else
0)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
14
else
13)
else
(if i.val < 1771 then
31
else
11))
else
(if i.val < 1774 then
(if i.val < 1773 then
13
else
0)
else
(if i.val < 1775 then
18
else
11))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
28
else
0)
else
(if i.val < 1779 then
0
else
0))
else
(if i.val < 1782 then
(if i.val < 1781 then
0
else
0)
else
(if i.val < 1783 then
0
else
0)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
0
else
0)
else
(if i.val < 1787 then
0
else
0))
else
(if i.val < 1790 then
(if i.val < 1789 then
0
else
0)
else
(if i.val < 1791 then
0
else
0))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
0
else
0)
else
(if i.val < 1795 then
0
else
0))
else
(if i.val < 1798 then
(if i.val < 1797 then
0
else
0)
else
(if i.val < 1799 then
0
else
0)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
0
else
0)
else
(if i.val < 1803 then
0
else
0))
else
(if i.val < 1806 then
(if i.val < 1805 then
14
else
29)
else
(if i.val < 1807 then
29
else
27))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
9
else
29)
else
(if i.val < 1811 then
0
else
29))
else
(if i.val < 1814 then
(if i.val < 1813 then
27
else
29)
else
(if i.val < 1815 then
9
else
0)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
29
else
24)
else
(if i.val < 1819 then
14
else
14))
else
(if i.val < 1822 then
(if i.val < 1821 then
31
else
14)
else
(if i.val < 1823 then
25
else
28)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
0
else
27)
else
(if i.val < 1827 then
29
else
23))
else
(if i.val < 1830 then
(if i.val < 1829 then
0
else
0)
else
(if i.val < 1831 then
32
else
14)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
9
else
0)
else
(if i.val < 1835 then
14
else
10))
else
(if i.val < 1838 then
(if i.val < 1837 then
0
else
0)
else
(if i.val < 1839 then
0
else
25))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
8
else
9)
else
(if i.val < 1843 then
10
else
32))
else
(if i.val < 1846 then
(if i.val < 1845 then
14
else
9)
else
(if i.val < 1847 then
8
else
8)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
0
else
0)
else
(if i.val < 1851 then
31
else
14))
else
(if i.val < 1854 then
(if i.val < 1853 then
0
else
0)
else
(if i.val < 1855 then
35
else
12))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
31
else
9)
else
(if i.val < 1859 then
10
else
10))
else
(if i.val < 1862 then
(if i.val < 1861 then
1
else
29)
else
(if i.val < 1863 then
0
else
26)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
9
else
6)
else
(if i.val < 1867 then
0
else
11))
else
(if i.val < 1870 then
(if i.val < 1869 then
17
else
0)
else
(if i.val < 1871 then
12
else
27))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
12
else
8)
else
(if i.val < 1875 then
27
else
25))
else
(if i.val < 1878 then
(if i.val < 1877 then
27
else
0)
else
(if i.val < 1879 then
31
else
0)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
0
else
14)
else
(if i.val < 1883 then
35
else
9))
else
(if i.val < 1886 then
(if i.val < 1885 then
7
else
0)
else
(if i.val < 1887 then
0
else
0)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
9
else
0)
else
(if i.val < 1891 then
8
else
0))
else
(if i.val < 1894 then
(if i.val < 1893 then
24
else
13)
else
(if i.val < 1895 then
29
else
9)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
31
else
17)
else
(if i.val < 1899 then
13
else
9))
else
(if i.val < 1902 then
(if i.val < 1901 then
0
else
32)
else
(if i.val < 1903 then
0
else
0))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
10
else
29)
else
(if i.val < 1907 then
12
else
25))
else
(if i.val < 1910 then
(if i.val < 1909 then
25
else
5)
else
(if i.val < 1911 then
24
else
25)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
14
else
9)
else
(if i.val < 1915 then
25
else
26))
else
(if i.val < 1918 then
(if i.val < 1917 then
8
else
25)
else
(if i.val < 1919 then
24
else
32)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
5
else
35)
else
(if i.val < 1923 then
14
else
10))
else
(if i.val < 1926 then
(if i.val < 1925 then
21
else
25)
else
(if i.val < 1927 then
10
else
0)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
0
else
31)
else
(if i.val < 1931 then
0
else
0))
else
(if i.val < 1934 then
(if i.val < 1933 then
0
else
6)
else
(if i.val < 1935 then
24
else
0))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
6
else
5)
else
(if i.val < 1939 then
23
else
0))
else
(if i.val < 1942 then
(if i.val < 1941 then
0
else
0)
else
(if i.val < 1943 then
0
else
0)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
25
else
18)
else
(if i.val < 1947 then
23
else
10))
else
(if i.val < 1950 then
(if i.val < 1949 then
8
else
25)
else
(if i.val < 1951 then
0
else
14)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
20
else
8)
else
(if i.val < 1955 then
14
else
10))
else
(if i.val < 1958 then
(if i.val < 1957 then
0
else
0)
else
(if i.val < 1959 then
0
else
0)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
0
else
0)
else
(if i.val < 1963 then
0
else
0))
else
(if i.val < 1966 then
(if i.val < 1965 then
0
else
8)
else
(if i.val < 1967 then
6
else
10))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
8
else
32)
else
(if i.val < 1971 then
0
else
27))
else
(if i.val < 1974 then
(if i.val < 1973 then
0
else
9)
else
(if i.val < 1975 then
0
else
0)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
0
else
11)
else
(if i.val < 1979 then
0
else
11))
else
(if i.val < 1982 then
(if i.val < 1981 then
10
else
0)
else
(if i.val < 1983 then
0
else
24))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
9
else
9)
else
(if i.val < 1987 then
0
else
0))
else
(if i.val < 1990 then
(if i.val < 1989 then
0
else
14)
else
(if i.val < 1991 then
14
else
14)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
0
else
0)
else
(if i.val < 1995 then
10
else
0))
else
(if i.val < 1998 then
(if i.val < 1997 then
11
else
11)
else
(if i.val < 1999 then
27
else
13))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
0
else
10)
else
(if i.val < 2003 then
23
else
0))
else
(if i.val < 2006 then
(if i.val < 2005 then
21
else
25)
else
(if i.val < 2007 then
9
else
14)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
28
else
22)
else
(if i.val < 2011 then
25
else
27))
else
(if i.val < 2014 then
(if i.val < 2013 then
21
else
23)
else
(if i.val < 2015 then
23
else
13)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
28
else
0)
else
(if i.val < 2019 then
29
else
0))
else
(if i.val < 2022 then
(if i.val < 2021 then
14
else
0)
else
(if i.val < 2023 then
29
else
14)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
14
else
0)
else
(if i.val < 2027 then
0
else
14))
else
(if i.val < 2030 then
(if i.val < 2029 then
8
else
9)
else
(if i.val < 2031 then
0
else
0))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
33
else
23)
else
(if i.val < 2035 then
23
else
23))
else
(if i.val < 2038 then
(if i.val < 2037 then
23
else
14)
else
(if i.val < 2039 then
14
else
16)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
28
else
1)
else
(if i.val < 2043 then
10
else
23))
else
(if i.val < 2046 then
(if i.val < 2045 then
0
else
18)
else
(if i.val < 2047 then
31
else
8)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0004 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
25
else
29)
else
(if i.val < 2051 then
0
else
29))
else
(if i.val < 2054 then
(if i.val < 2053 then
23
else
0)
else
(if i.val < 2055 then
14
else
32)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
14
else
0)
else
(if i.val < 2059 then
23
else
0))
else
(if i.val < 2062 then
(if i.val < 2061 then
0
else
27)
else
(if i.val < 2063 then
29
else
23))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
14
else
14)
else
(if i.val < 2067 then
14
else
14))
else
(if i.val < 2070 then
(if i.val < 2069 then
28
else
10)
else
(if i.val < 2071 then
10
else
35)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
0
else
0)
else
(if i.val < 2075 then
27
else
29))
else
(if i.val < 2078 then
(if i.val < 2077 then
31
else
29)
else
(if i.val < 2079 then
29
else
29)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
9
else
9)
else
(if i.val < 2083 then
16
else
29))
else
(if i.val < 2086 then
(if i.val < 2085 then
0
else
1)
else
(if i.val < 2087 then
8
else
28)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
0
else
14)
else
(if i.val < 2091 then
1
else
35))
else
(if i.val < 2094 then
(if i.val < 2093 then
6
else
29)
else
(if i.val < 2095 then
22
else
12))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
29
else
0)
else
(if i.val < 2099 then
0
else
22))
else
(if i.val < 2102 then
(if i.val < 2101 then
0
else
31)
else
(if i.val < 2103 then
14
else
0)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
0
else
14)
else
(if i.val < 2107 then
28
else
10))
else
(if i.val < 2110 then
(if i.val < 2109 then
29
else
0)
else
(if i.val < 2111 then
0
else
14))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
14
else
25)
else
(if i.val < 2115 then
30
else
0))
else
(if i.val < 2118 then
(if i.val < 2117 then
12
else
9)
else
(if i.val < 2119 then
0
else
0)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
14
else
0)
else
(if i.val < 2123 then
31
else
13))
else
(if i.val < 2126 then
(if i.val < 2125 then
12
else
29)
else
(if i.val < 2127 then
21
else
26))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
25
else
0)
else
(if i.val < 2131 then
1
else
32))
else
(if i.val < 2134 then
(if i.val < 2133 then
33
else
0)
else
(if i.val < 2135 then
8
else
0)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
17
else
21)
else
(if i.val < 2139 then
21
else
8))
else
(if i.val < 2142 then
(if i.val < 2141 then
17
else
22)
else
(if i.val < 2143 then
0
else
0)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
23
else
22)
else
(if i.val < 2147 then
27
else
35))
else
(if i.val < 2150 then
(if i.val < 2149 then
0
else
2)
else
(if i.val < 2151 then
16
else
31)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
14
else
14)
else
(if i.val < 2155 then
2
else
13))
else
(if i.val < 2158 then
(if i.val < 2157 then
4
else
13)
else
(if i.val < 2159 then
17
else
16))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
32
else
1)
else
(if i.val < 2163 then
0
else
33))
else
(if i.val < 2166 then
(if i.val < 2165 then
0
else
1)
else
(if i.val < 2167 then
13
else
28)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
0
else
29)
else
(if i.val < 2171 then
14
else
0))
else
(if i.val < 2174 then
(if i.val < 2173 then
16
else
0)
else
(if i.val < 2175 then
0
else
12)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
0
else
0)
else
(if i.val < 2179 then
0
else
8))
else
(if i.val < 2182 then
(if i.val < 2181 then
0
else
0)
else
(if i.val < 2183 then
2
else
0)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
28
else
0)
else
(if i.val < 2187 then
0
else
0))
else
(if i.val < 2190 then
(if i.val < 2189 then
0
else
29)
else
(if i.val < 2191 then
29
else
0))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
14
else
0)
else
(if i.val < 2195 then
14
else
28))
else
(if i.val < 2198 then
(if i.val < 2197 then
8
else
0)
else
(if i.val < 2199 then
32
else
0)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
1
else
0)
else
(if i.val < 2203 then
29
else
23))
else
(if i.val < 2206 then
(if i.val < 2205 then
23
else
23)
else
(if i.val < 2207 then
9
else
0)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
21
else
14)
else
(if i.val < 2211 then
8
else
8))
else
(if i.val < 2214 then
(if i.val < 2213 then
5
else
28)
else
(if i.val < 2215 then
0
else
0)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
25
else
21)
else
(if i.val < 2219 then
17
else
8))
else
(if i.val < 2222 then
(if i.val < 2221 then
0
else
0)
else
(if i.val < 2223 then
0
else
3))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
3
else
14)
else
(if i.val < 2227 then
3
else
3))
else
(if i.val < 2230 then
(if i.val < 2229 then
0
else
8)
else
(if i.val < 2231 then
25
else
35)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
21
else
0)
else
(if i.val < 2235 then
0
else
9))
else
(if i.val < 2238 then
(if i.val < 2237 then
0
else
0)
else
(if i.val < 2239 then
4
else
23))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
29
else
25)
else
(if i.val < 2243 then
31
else
9))
else
(if i.val < 2246 then
(if i.val < 2245 then
35
else
0)
else
(if i.val < 2247 then
1
else
16)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
14
else
17)
else
(if i.val < 2251 then
23
else
20))
else
(if i.val < 2254 then
(if i.val < 2253 then
33
else
16)
else
(if i.val < 2255 then
0
else
32))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
24
else
8)
else
(if i.val < 2259 then
25
else
26))
else
(if i.val < 2262 then
(if i.val < 2261 then
0
else
9)
else
(if i.val < 2263 then
0
else
0)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
10
else
23)
else
(if i.val < 2267 then
0
else
0))
else
(if i.val < 2270 then
(if i.val < 2269 then
0
else
10)
else
(if i.val < 2271 then
16
else
25)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
23
else
28)
else
(if i.val < 2275 then
14
else
23))
else
(if i.val < 2278 then
(if i.val < 2277 then
8
else
8)
else
(if i.val < 2279 then
23
else
6)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
8
else
23)
else
(if i.val < 2283 then
14
else
0))
else
(if i.val < 2286 then
(if i.val < 2285 then
29
else
0)
else
(if i.val < 2287 then
0
else
0))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
23
else
23)
else
(if i.val < 2291 then
27
else
23))
else
(if i.val < 2294 then
(if i.val < 2293 then
27
else
9)
else
(if i.val < 2295 then
10
else
29)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
25
else
17)
else
(if i.val < 2299 then
8
else
14))
else
(if i.val < 2302 then
(if i.val < 2301 then
0
else
0)
else
(if i.val < 2303 then
10
else
0))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
24
else
0)
else
(if i.val < 2307 then
0
else
8))
else
(if i.val < 2310 then
(if i.val < 2309 then
0
else
0)
else
(if i.val < 2311 then
0
else
0)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
0
else
0)
else
(if i.val < 2315 then
0
else
0))
else
(if i.val < 2318 then
(if i.val < 2317 then
0
else
0)
else
(if i.val < 2319 then
0
else
0))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
0
else
0)
else
(if i.val < 2323 then
0
else
0))
else
(if i.val < 2326 then
(if i.val < 2325 then
10
else
8)
else
(if i.val < 2327 then
0
else
0)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
14
else
0)
else
(if i.val < 2331 then
0
else
21))
else
(if i.val < 2334 then
(if i.val < 2333 then
29
else
27)
else
(if i.val < 2335 then
10
else
11)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
10
else
0)
else
(if i.val < 2339 then
0
else
8))
else
(if i.val < 2342 then
(if i.val < 2341 then
0
else
9)
else
(if i.val < 2343 then
0
else
12)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
0
else
18)
else
(if i.val < 2347 then
11
else
10))
else
(if i.val < 2350 then
(if i.val < 2349 then
10
else
0)
else
(if i.val < 2351 then
0
else
0))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
27
else
24)
else
(if i.val < 2355 then
19
else
25))
else
(if i.val < 2358 then
(if i.val < 2357 then
0
else
3)
else
(if i.val < 2359 then
0
else
26)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
0
else
14)
else
(if i.val < 2363 then
17
else
0))
else
(if i.val < 2366 then
(if i.val < 2365 then
27
else
0)
else
(if i.val < 2367 then
14
else
14))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
23
else
31)
else
(if i.val < 2371 then
28
else
14))
else
(if i.val < 2374 then
(if i.val < 2373 then
0
else
0)
else
(if i.val < 2375 then
0
else
9)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
0
else
10)
else
(if i.val < 2379 then
28
else
10))
else
(if i.val < 2382 then
(if i.val < 2381 then
10
else
0)
else
(if i.val < 2383 then
6
else
0))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
0
else
10)
else
(if i.val < 2387 then
27
else
9))
else
(if i.val < 2390 then
(if i.val < 2389 then
0
else
17)
else
(if i.val < 2391 then
0
else
12)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
0
else
28)
else
(if i.val < 2395 then
0
else
10))
else
(if i.val < 2398 then
(if i.val < 2397 then
0
else
0)
else
(if i.val < 2399 then
28
else
0)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
14
else
13)
else
(if i.val < 2403 then
0
else
23))
else
(if i.val < 2406 then
(if i.val < 2405 then
8
else
0)
else
(if i.val < 2407 then
26
else
0)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
6
else
25)
else
(if i.val < 2411 then
18
else
9))
else
(if i.val < 2414 then
(if i.val < 2413 then
16
else
12)
else
(if i.val < 2415 then
23
else
0))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
25
else
0)
else
(if i.val < 2419 then
0
else
0))
else
(if i.val < 2422 then
(if i.val < 2421 then
14
else
0)
else
(if i.val < 2423 then
0
else
28)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
8
else
0)
else
(if i.val < 2427 then
10
else
0))
else
(if i.val < 2430 then
(if i.val < 2429 then
0
else
0)
else
(if i.val < 2431 then
0
else
25)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
11
else
0)
else
(if i.val < 2435 then
8
else
13))
else
(if i.val < 2438 then
(if i.val < 2437 then
5
else
25)
else
(if i.val < 2439 then
23
else
24)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
0
else
3)
else
(if i.val < 2443 then
4
else
4))
else
(if i.val < 2446 then
(if i.val < 2445 then
0
else
23)
else
(if i.val < 2447 then
23
else
22))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
23
else
23)
else
(if i.val < 2451 then
23
else
0))
else
(if i.val < 2454 then
(if i.val < 2453 then
17
else
33)
else
(if i.val < 2455 then
27
else
19)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
27
else
16)
else
(if i.val < 2459 then
0
else
10))
else
(if i.val < 2462 then
(if i.val < 2461 then
28
else
2)
else
(if i.val < 2463 then
0
else
17)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
29
else
23)
else
(if i.val < 2467 then
23
else
0))
else
(if i.val < 2470 then
(if i.val < 2469 then
24
else
29)
else
(if i.val < 2471 then
8
else
23)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
25
else
23)
else
(if i.val < 2475 then
8
else
23))
else
(if i.val < 2478 then
(if i.val < 2477 then
25
else
0)
else
(if i.val < 2479 then
27
else
23))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
23
else
23)
else
(if i.val < 2483 then
12
else
17))
else
(if i.val < 2486 then
(if i.val < 2485 then
29
else
0)
else
(if i.val < 2487 then
14
else
29)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
4
else
33)
else
(if i.val < 2491 then
0
else
0))
else
(if i.val < 2494 then
(if i.val < 2493 then
0
else
0)
else
(if i.val < 2495 then
0
else
0))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
0
else
0)
else
(if i.val < 2499 then
0
else
0))
else
(if i.val < 2502 then
(if i.val < 2501 then
0
else
0)
else
(if i.val < 2503 then
9
else
0)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
0
else
0)
else
(if i.val < 2507 then
25
else
27))
else
(if i.val < 2510 then
(if i.val < 2509 then
8
else
28)
else
(if i.val < 2511 then
11
else
10))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
0
else
8)
else
(if i.val < 2515 then
24
else
27))
else
(if i.val < 2518 then
(if i.val < 2517 then
0
else
0)
else
(if i.val < 2519 then
32
else
28)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
28
else
13)
else
(if i.val < 2523 then
27
else
29))
else
(if i.val < 2526 then
(if i.val < 2525 then
29
else
0)
else
(if i.val < 2527 then
14
else
35)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
33
else
9)
else
(if i.val < 2531 then
8
else
29))
else
(if i.val < 2534 then
(if i.val < 2533 then
23
else
9)
else
(if i.val < 2535 then
17
else
0)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
0
else
23)
else
(if i.val < 2539 then
9
else
23))
else
(if i.val < 2542 then
(if i.val < 2541 then
29
else
29)
else
(if i.val < 2543 then
9
else
0))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
9
else
25)
else
(if i.val < 2547 then
28
else
27))
else
(if i.val < 2550 then
(if i.val < 2549 then
29
else
23)
else
(if i.val < 2551 then
0
else
0)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
0
else
0)
else
(if i.val < 2555 then
0
else
27))
else
(if i.val < 2558 then
(if i.val < 2557 then
0
else
0)
else
(if i.val < 2559 then
0
else
0)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0005 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
9
else
18)
else
(if i.val < 2563 then
0
else
29))
else
(if i.val < 2566 then
(if i.val < 2565 then
27
else
29)
else
(if i.val < 2567 then
25
else
10)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
9
else
23)
else
(if i.val < 2571 then
24
else
0))
else
(if i.val < 2574 then
(if i.val < 2573 then
8
else
5)
else
(if i.val < 2575 then
22
else
6))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
8
else
35)
else
(if i.val < 2579 then
8
else
33))
else
(if i.val < 2582 then
(if i.val < 2581 then
8
else
8)
else
(if i.val < 2583 then
27
else
35)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
24
else
33)
else
(if i.val < 2587 then
22
else
0))
else
(if i.val < 2590 then
(if i.val < 2589 then
0
else
33)
else
(if i.val < 2591 then
25
else
0)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
0
else
14)
else
(if i.val < 2595 then
25
else
18))
else
(if i.val < 2598 then
(if i.val < 2597 then
0
else
14)
else
(if i.val < 2599 then
0
else
14)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
10
else
11)
else
(if i.val < 2603 then
35
else
11))
else
(if i.val < 2606 then
(if i.val < 2605 then
35
else
10)
else
(if i.val < 2607 then
16
else
9))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
8
else
11)
else
(if i.val < 2611 then
0
else
9))
else
(if i.val < 2614 then
(if i.val < 2613 then
18
else
14)
else
(if i.val < 2615 then
0
else
35)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
21
else
28)
else
(if i.val < 2619 then
13
else
0))
else
(if i.val < 2622 then
(if i.val < 2621 then
0
else
0)
else
(if i.val < 2623 then
0
else
26))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
9
else
0)
else
(if i.val < 2627 then
27
else
0))
else
(if i.val < 2630 then
(if i.val < 2629 then
24
else
14)
else
(if i.val < 2631 then
0
else
0)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
22
else
21)
else
(if i.val < 2635 then
22
else
5))
else
(if i.val < 2638 then
(if i.val < 2637 then
22
else
22)
else
(if i.val < 2639 then
22
else
8))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
0
else
25)
else
(if i.val < 2643 then
0
else
8))
else
(if i.val < 2646 then
(if i.val < 2645 then
6
else
21)
else
(if i.val < 2647 then
0
else
8)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
19
else
10)
else
(if i.val < 2651 then
0
else
21))
else
(if i.val < 2654 then
(if i.val < 2653 then
0
else
18)
else
(if i.val < 2655 then
18
else
22)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
0
else
0)
else
(if i.val < 2659 then
22
else
20))
else
(if i.val < 2662 then
(if i.val < 2661 then
0
else
17)
else
(if i.val < 2663 then
17
else
0)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
0
else
18)
else
(if i.val < 2667 then
18
else
6))
else
(if i.val < 2670 then
(if i.val < 2669 then
0
else
9)
else
(if i.val < 2671 then
17
else
21))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
31
else
19)
else
(if i.val < 2675 then
8
else
21))
else
(if i.val < 2678 then
(if i.val < 2677 then
0
else
0)
else
(if i.val < 2679 then
0
else
0)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
14
else
0)
else
(if i.val < 2683 then
10
else
21))
else
(if i.val < 2686 then
(if i.val < 2685 then
0
else
0)
else
(if i.val < 2687 then
25
else
21)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
0
else
0)
else
(if i.val < 2691 then
5
else
0))
else
(if i.val < 2694 then
(if i.val < 2693 then
33
else
19)
else
(if i.val < 2695 then
9
else
0)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
35
else
11)
else
(if i.val < 2699 then
25
else
10))
else
(if i.val < 2702 then
(if i.val < 2701 then
8
else
11)
else
(if i.val < 2703 then
0
else
27))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
35
else
28)
else
(if i.val < 2707 then
0
else
10))
else
(if i.val < 2710 then
(if i.val < 2709 then
11
else
27)
else
(if i.val < 2711 then
10
else
8)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
11
else
11)
else
(if i.val < 2715 then
27
else
28))
else
(if i.val < 2718 then
(if i.val < 2717 then
0
else
17)
else
(if i.val < 2719 then
28
else
0)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
0
else
10)
else
(if i.val < 2723 then
32
else
18))
else
(if i.val < 2726 then
(if i.val < 2725 then
0
else
16)
else
(if i.val < 2727 then
3
else
32)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
10
else
8)
else
(if i.val < 2731 then
11
else
14))
else
(if i.val < 2734 then
(if i.val < 2733 then
33
else
11)
else
(if i.val < 2735 then
21
else
11))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
13
else
28)
else
(if i.val < 2739 then
8
else
0))
else
(if i.val < 2742 then
(if i.val < 2741 then
0
else
0)
else
(if i.val < 2743 then
0
else
0)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
0
else
0)
else
(if i.val < 2747 then
0
else
0))
else
(if i.val < 2750 then
(if i.val < 2749 then
0
else
0)
else
(if i.val < 2751 then
0
else
0))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
25
else
6)
else
(if i.val < 2755 then
22
else
24))
else
(if i.val < 2758 then
(if i.val < 2757 then
0
else
10)
else
(if i.val < 2759 then
10
else
24)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
24
else
8)
else
(if i.val < 2763 then
7
else
0))
else
(if i.val < 2766 then
(if i.val < 2765 then
0
else
0)
else
(if i.val < 2767 then
0
else
25))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
7
else
8)
else
(if i.val < 2771 then
8
else
20))
else
(if i.val < 2774 then
(if i.val < 2773 then
33
else
21)
else
(if i.val < 2775 then
0
else
25)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
0
else
21)
else
(if i.val < 2779 then
24
else
0))
else
(if i.val < 2782 then
(if i.val < 2781 then
0
else
0)
else
(if i.val < 2783 then
33
else
0)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
14
else
0)
else
(if i.val < 2787 then
22
else
9))
else
(if i.val < 2790 then
(if i.val < 2789 then
21
else
6)
else
(if i.val < 2791 then
22
else
0)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
20
else
27)
else
(if i.val < 2795 then
18
else
8))
else
(if i.val < 2798 then
(if i.val < 2797 then
31
else
14)
else
(if i.val < 2799 then
0
else
0))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
1
else
6)
else
(if i.val < 2803 then
9
else
35))
else
(if i.val < 2806 then
(if i.val < 2805 then
35
else
35)
else
(if i.val < 2807 then
6
else
23)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
14
else
6)
else
(if i.val < 2811 then
0
else
8))
else
(if i.val < 2814 then
(if i.val < 2813 then
0
else
20)
else
(if i.val < 2815 then
8
else
21))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
5
else
32)
else
(if i.val < 2819 then
16
else
22))
else
(if i.val < 2822 then
(if i.val < 2821 then
32
else
25)
else
(if i.val < 2823 then
0
else
14)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
18
else
0)
else
(if i.val < 2827 then
26
else
10))
else
(if i.val < 2830 then
(if i.val < 2829 then
32
else
11)
else
(if i.val < 2831 then
25
else
2))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
0
else
14)
else
(if i.val < 2835 then
0
else
14))
else
(if i.val < 2838 then
(if i.val < 2837 then
0
else
1)
else
(if i.val < 2839 then
35
else
0)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
0
else
0)
else
(if i.val < 2843 then
0
else
14))
else
(if i.val < 2846 then
(if i.val < 2845 then
35
else
0)
else
(if i.val < 2847 then
6
else
0)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
0
else
12)
else
(if i.val < 2851 then
11
else
25))
else
(if i.val < 2854 then
(if i.val < 2853 then
0
else
0)
else
(if i.val < 2855 then
17
else
24)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
8
else
24)
else
(if i.val < 2859 then
0
else
0))
else
(if i.val < 2862 then
(if i.val < 2861 then
0
else
21)
else
(if i.val < 2863 then
0
else
27))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
0
else
35)
else
(if i.val < 2867 then
35
else
33))
else
(if i.val < 2870 then
(if i.val < 2869 then
14
else
32)
else
(if i.val < 2871 then
8
else
0)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
0
else
0)
else
(if i.val < 2875 then
0
else
26))
else
(if i.val < 2878 then
(if i.val < 2877 then
0
else
14)
else
(if i.val < 2879 then
11
else
0))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
0
else
0)
else
(if i.val < 2883 then
0
else
0))
else
(if i.val < 2886 then
(if i.val < 2885 then
9
else
0)
else
(if i.val < 2887 then
1
else
33)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
19
else
14)
else
(if i.val < 2891 then
0
else
0))
else
(if i.val < 2894 then
(if i.val < 2893 then
0
else
14)
else
(if i.val < 2895 then
16
else
33))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
29
else
8)
else
(if i.val < 2899 then
35
else
13))
else
(if i.val < 2902 then
(if i.val < 2901 then
8
else
10)
else
(if i.val < 2903 then
27
else
11)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
12
else
12)
else
(if i.val < 2907 then
8
else
18))
else
(if i.val < 2910 then
(if i.val < 2909 then
0
else
13)
else
(if i.val < 2911 then
11
else
11)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
31
else
10)
else
(if i.val < 2915 then
31
else
0))
else
(if i.val < 2918 then
(if i.val < 2917 then
18
else
10)
else
(if i.val < 2919 then
11
else
11)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
10
else
25)
else
(if i.val < 2923 then
0
else
12))
else
(if i.val < 2926 then
(if i.val < 2925 then
1
else
11)
else
(if i.val < 2927 then
11
else
0))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
6
else
0)
else
(if i.val < 2931 then
0
else
31))
else
(if i.val < 2934 then
(if i.val < 2933 then
0
else
0)
else
(if i.val < 2935 then
17
else
9)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
31
else
14)
else
(if i.val < 2939 then
0
else
0))
else
(if i.val < 2942 then
(if i.val < 2941 then
10
else
28)
else
(if i.val < 2943 then
0
else
10)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
0
else
0)
else
(if i.val < 2947 then
21
else
10))
else
(if i.val < 2950 then
(if i.val < 2949 then
10
else
0)
else
(if i.val < 2951 then
0
else
0)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
14
else
31)
else
(if i.val < 2955 then
17
else
28))
else
(if i.val < 2958 then
(if i.val < 2957 then
8
else
8)
else
(if i.val < 2959 then
32
else
14))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
28
else
17)
else
(if i.val < 2963 then
3
else
31))
else
(if i.val < 2966 then
(if i.val < 2965 then
31
else
16)
else
(if i.val < 2967 then
27
else
35)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
22
else
5)
else
(if i.val < 2971 then
0
else
0))
else
(if i.val < 2974 then
(if i.val < 2973 then
0
else
11)
else
(if i.val < 2975 then
11
else
0)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
32
else
20)
else
(if i.val < 2979 then
17
else
11))
else
(if i.val < 2982 then
(if i.val < 2981 then
11
else
29)
else
(if i.val < 2983 then
0
else
18)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
13
else
11)
else
(if i.val < 2987 then
0
else
18))
else
(if i.val < 2990 then
(if i.val < 2989 then
10
else
11)
else
(if i.val < 2991 then
0
else
0))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
0
else
0)
else
(if i.val < 2995 then
0
else
0))
else
(if i.val < 2998 then
(if i.val < 2997 then
0
else
0)
else
(if i.val < 2999 then
0
else
0)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
0
else
0)
else
(if i.val < 3003 then
0
else
0))
else
(if i.val < 3006 then
(if i.val < 3005 then
0
else
0)
else
(if i.val < 3007 then
0
else
0))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
0
else
0)
else
(if i.val < 3011 then
0
else
0))
else
(if i.val < 3014 then
(if i.val < 3013 then
0
else
0)
else
(if i.val < 3015 then
10
else
9)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
29
else
29)
else
(if i.val < 3019 then
27
else
0))
else
(if i.val < 3022 then
(if i.val < 3021 then
9
else
29)
else
(if i.val < 3023 then
13
else
16))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
29
else
35)
else
(if i.val < 3027 then
29
else
23))
else
(if i.val < 3030 then
(if i.val < 3029 then
14
else
14)
else
(if i.val < 3031 then
23
else
14)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
28
else
0)
else
(if i.val < 3035 then
23
else
23))
else
(if i.val < 3038 then
(if i.val < 3037 then
28
else
12)
else
(if i.val < 3039 then
35
else
25)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
31
else
8)
else
(if i.val < 3043 then
31
else
30))
else
(if i.val < 3046 then
(if i.val < 3045 then
27
else
13)
else
(if i.val < 3047 then
12
else
31)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
9
else
10)
else
(if i.val < 3051 then
10
else
1))
else
(if i.val < 3054 then
(if i.val < 3053 then
11
else
25)
else
(if i.val < 3055 then
0
else
0))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
35
else
35)
else
(if i.val < 3059 then
27
else
10))
else
(if i.val < 3062 then
(if i.val < 3061 then
26
else
28)
else
(if i.val < 3063 then
10
else
9)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
29
else
29)
else
(if i.val < 3067 then
23
else
11))
else
(if i.val < 3070 then
(if i.val < 3069 then
23
else
10)
else
(if i.val < 3071 then
12
else
7)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0006 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
12
else
16)
else
(if i.val < 3075 then
30
else
3))
else
(if i.val < 3078 then
(if i.val < 3077 then
30
else
12)
else
(if i.val < 3079 then
14
else
0)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
14
else
9)
else
(if i.val < 3083 then
6
else
16))
else
(if i.val < 3086 then
(if i.val < 3085 then
14
else
10)
else
(if i.val < 3087 then
0
else
0))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
0
else
20)
else
(if i.val < 3091 then
8
else
28))
else
(if i.val < 3094 then
(if i.val < 3093 then
6
else
31)
else
(if i.val < 3095 then
32
else
28)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
13
else
31)
else
(if i.val < 3099 then
7
else
17))
else
(if i.val < 3102 then
(if i.val < 3101 then
29
else
12)
else
(if i.val < 3103 then
9
else
13)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
9
else
0)
else
(if i.val < 3107 then
21
else
5))
else
(if i.val < 3110 then
(if i.val < 3109 then
29
else
26)
else
(if i.val < 3111 then
9
else
25)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
10
else
26)
else
(if i.val < 3115 then
8
else
25))
else
(if i.val < 3118 then
(if i.val < 3117 then
26
else
32)
else
(if i.val < 3119 then
5
else
24))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
21
else
34)
else
(if i.val < 3123 then
21
else
9))
else
(if i.val < 3126 then
(if i.val < 3125 then
6
else
26)
else
(if i.val < 3127 then
31
else
26)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
26
else
5)
else
(if i.val < 3131 then
29
else
32))
else
(if i.val < 3134 then
(if i.val < 3133 then
33
else
24)
else
(if i.val < 3135 then
2
else
19))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
16
else
26)
else
(if i.val < 3139 then
33
else
27))
else
(if i.val < 3142 then
(if i.val < 3141 then
32
else
33)
else
(if i.val < 3143 then
29
else
0)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
9
else
6)
else
(if i.val < 3147 then
6
else
22))
else
(if i.val < 3150 then
(if i.val < 3149 then
12
else
29)
else
(if i.val < 3151 then
0
else
6))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
23
else
16)
else
(if i.val < 3155 then
20
else
14))
else
(if i.val < 3158 then
(if i.val < 3157 then
18
else
8)
else
(if i.val < 3159 then
20
else
8)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
10
else
0)
else
(if i.val < 3163 then
0
else
0))
else
(if i.val < 3166 then
(if i.val < 3165 then
32
else
0)
else
(if i.val < 3167 then
0
else
8)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
0
else
6)
else
(if i.val < 3171 then
8
else
28))
else
(if i.val < 3174 then
(if i.val < 3173 then
13
else
1)
else
(if i.val < 3175 then
8
else
0)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
11
else
10)
else
(if i.val < 3179 then
33
else
0))
else
(if i.val < 3182 then
(if i.val < 3181 then
29
else
17)
else
(if i.val < 3183 then
17
else
25))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
8
else
32)
else
(if i.val < 3187 then
31
else
1))
else
(if i.val < 3190 then
(if i.val < 3189 then
8
else
32)
else
(if i.val < 3191 then
0
else
0)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
8
else
8)
else
(if i.val < 3195 then
11
else
12))
else
(if i.val < 3198 then
(if i.val < 3197 then
11
else
30)
else
(if i.val < 3199 then
0
else
29)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
26
else
13)
else
(if i.val < 3203 then
31
else
0))
else
(if i.val < 3206 then
(if i.val < 3205 then
12
else
32)
else
(if i.val < 3207 then
13
else
8)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
21
else
26)
else
(if i.val < 3211 then
21
else
14))
else
(if i.val < 3214 then
(if i.val < 3213 then
14
else
14)
else
(if i.val < 3215 then
29
else
23))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
14
else
14)
else
(if i.val < 3219 then
23
else
14))
else
(if i.val < 3222 then
(if i.val < 3221 then
14
else
13)
else
(if i.val < 3223 then
13
else
6)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
26
else
32)
else
(if i.val < 3227 then
33
else
20))
else
(if i.val < 3230 then
(if i.val < 3229 then
33
else
19)
else
(if i.val < 3231 then
21
else
22)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
23
else
23)
else
(if i.val < 3235 then
23
else
14))
else
(if i.val < 3238 then
(if i.val < 3237 then
16
else
31)
else
(if i.val < 3239 then
14
else
14)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
13
else
13)
else
(if i.val < 3243 then
16
else
28))
else
(if i.val < 3246 then
(if i.val < 3245 then
20
else
27)
else
(if i.val < 3247 then
14
else
33))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
1
else
26)
else
(if i.val < 3251 then
29
else
21))
else
(if i.val < 3254 then
(if i.val < 3253 then
31
else
2)
else
(if i.val < 3255 then
12
else
29)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
26
else
14)
else
(if i.val < 3259 then
16
else
0))
else
(if i.val < 3262 then
(if i.val < 3261 then
23
else
23)
else
(if i.val < 3263 then
14
else
4))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
16
else
14)
else
(if i.val < 3267 then
9
else
9))
else
(if i.val < 3270 then
(if i.val < 3269 then
21
else
14)
else
(if i.val < 3271 then
27
else
27)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
30
else
10)
else
(if i.val < 3275 then
0
else
9))
else
(if i.val < 3278 then
(if i.val < 3277 then
0
else
3)
else
(if i.val < 3279 then
27
else
1))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
9
else
9)
else
(if i.val < 3283 then
29
else
27))
else
(if i.val < 3286 then
(if i.val < 3285 then
13
else
30)
else
(if i.val < 3287 then
9
else
27)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
14
else
27)
else
(if i.val < 3291 then
0
else
28))
else
(if i.val < 3294 then
(if i.val < 3293 then
31
else
27)
else
(if i.val < 3295 then
13
else
30)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
26
else
29)
else
(if i.val < 3299 then
10
else
16))
else
(if i.val < 3302 then
(if i.val < 3301 then
19
else
29)
else
(if i.val < 3303 then
0
else
27)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
22
else
0)
else
(if i.val < 3307 then
27
else
23))
else
(if i.val < 3310 then
(if i.val < 3309 then
14
else
10)
else
(if i.val < 3311 then
11
else
13))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
14
else
18)
else
(if i.val < 3315 then
10
else
21))
else
(if i.val < 3318 then
(if i.val < 3317 then
29
else
14)
else
(if i.val < 3319 then
29
else
8)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
35
else
0)
else
(if i.val < 3323 then
0
else
14))
else
(if i.val < 3326 then
(if i.val < 3325 then
29
else
0)
else
(if i.val < 3327 then
29
else
16))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
10
else
22)
else
(if i.val < 3331 then
13
else
12))
else
(if i.val < 3334 then
(if i.val < 3333 then
14
else
29)
else
(if i.val < 3335 then
8
else
25)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
27
else
21)
else
(if i.val < 3339 then
17
else
22))
else
(if i.val < 3342 then
(if i.val < 3341 then
33
else
16)
else
(if i.val < 3343 then
25
else
17))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
17
else
25)
else
(if i.val < 3347 then
17
else
22))
else
(if i.val < 3350 then
(if i.val < 3349 then
23
else
0)
else
(if i.val < 3351 then
21
else
7)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
14
else
9)
else
(if i.val < 3355 then
17
else
4))
else
(if i.val < 3358 then
(if i.val < 3357 then
14
else
13)
else
(if i.val < 3359 then
0
else
13)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
19
else
17)
else
(if i.val < 3363 then
1
else
33))
else
(if i.val < 3366 then
(if i.val < 3365 then
0
else
33)
else
(if i.val < 3367 then
13
else
29)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
9
else
14)
else
(if i.val < 3371 then
33
else
19))
else
(if i.val < 3374 then
(if i.val < 3373 then
0
else
4)
else
(if i.val < 3375 then
19
else
35))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
0
else
19)
else
(if i.val < 3379 then
0
else
6))
else
(if i.val < 3382 then
(if i.val < 3381 then
21
else
12)
else
(if i.val < 3383 then
20
else
21)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
10
else
31)
else
(if i.val < 3387 then
20
else
8))
else
(if i.val < 3390 then
(if i.val < 3389 then
33
else
32)
else
(if i.val < 3391 then
0
else
0))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
0
else
29)
else
(if i.val < 3395 then
23
else
0))
else
(if i.val < 3398 then
(if i.val < 3397 then
27
else
0)
else
(if i.val < 3399 then
23
else
14)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
14
else
14)
else
(if i.val < 3403 then
1
else
14))
else
(if i.val < 3406 then
(if i.val < 3405 then
0
else
21)
else
(if i.val < 3407 then
33
else
31))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
1
else
19)
else
(if i.val < 3411 then
26
else
23))
else
(if i.val < 3414 then
(if i.val < 3413 then
12
else
23)
else
(if i.val < 3415 then
23
else
23)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
22
else
26)
else
(if i.val < 3419 then
21
else
8))
else
(if i.val < 3422 then
(if i.val < 3421 then
6
else
0)
else
(if i.val < 3423 then
23
else
32)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
22
else
9)
else
(if i.val < 3427 then
8
else
33))
else
(if i.val < 3430 then
(if i.val < 3429 then
33
else
34)
else
(if i.val < 3431 then
3
else
3)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
14
else
30)
else
(if i.val < 3435 then
3
else
9))
else
(if i.val < 3438 then
(if i.val < 3437 then
28
else
0)
else
(if i.val < 3439 then
21
else
7))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
23
else
35)
else
(if i.val < 3443 then
1
else
0))
else
(if i.val < 3446 then
(if i.val < 3445 then
0
else
9)
else
(if i.val < 3447 then
23
else
29)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
26
else
23)
else
(if i.val < 3451 then
6
else
33))
else
(if i.val < 3454 then
(if i.val < 3453 then
14
else
32)
else
(if i.val < 3455 then
28
else
13)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
29
else
28)
else
(if i.val < 3459 then
16
else
9))
else
(if i.val < 3462 then
(if i.val < 3461 then
9
else
13)
else
(if i.val < 3463 then
8
else
0)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
0
else
18)
else
(if i.val < 3467 then
24
else
23))
else
(if i.val < 3470 then
(if i.val < 3469 then
28
else
9)
else
(if i.val < 3471 then
0
else
26))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
0
else
23)
else
(if i.val < 3475 then
33
else
23))
else
(if i.val < 3478 then
(if i.val < 3477 then
21
else
23)
else
(if i.val < 3479 then
22
else
0)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
0
else
0)
else
(if i.val < 3483 then
0
else
23))
else
(if i.val < 3486 then
(if i.val < 3485 then
14
else
33)
else
(if i.val < 3487 then
27
else
29)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
29
else
25)
else
(if i.val < 3491 then
5
else
35))
else
(if i.val < 3494 then
(if i.val < 3493 then
14
else
5)
else
(if i.val < 3495 then
23
else
19)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
8
else
0)
else
(if i.val < 3499 then
8
else
0))
else
(if i.val < 3502 then
(if i.val < 3501 then
0
else
0)
else
(if i.val < 3503 then
0
else
0))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
0
else
0)
else
(if i.val < 3507 then
0
else
0))
else
(if i.val < 3510 then
(if i.val < 3509 then
0
else
0)
else
(if i.val < 3511 then
0
else
0)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
0
else
11)
else
(if i.val < 3515 then
6
else
9))
else
(if i.val < 3518 then
(if i.val < 3517 then
8
else
8)
else
(if i.val < 3519 then
11
else
6))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
21
else
12)
else
(if i.val < 3523 then
9
else
7))
else
(if i.val < 3526 then
(if i.val < 3525 then
9
else
0)
else
(if i.val < 3527 then
24
else
25)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
35
else
22)
else
(if i.val < 3531 then
12
else
29))
else
(if i.val < 3534 then
(if i.val < 3533 then
0
else
11)
else
(if i.val < 3535 then
11
else
0))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
8
else
8)
else
(if i.val < 3539 then
28
else
25))
else
(if i.val < 3542 then
(if i.val < 3541 then
21
else
28)
else
(if i.val < 3543 then
0
else
11)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
3
else
33)
else
(if i.val < 3547 then
0
else
13))
else
(if i.val < 3550 then
(if i.val < 3549 then
18
else
35)
else
(if i.val < 3551 then
23
else
14)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
33
else
8)
else
(if i.val < 3555 then
0
else
0))
else
(if i.val < 3558 then
(if i.val < 3557 then
10
else
0)
else
(if i.val < 3559 then
29
else
11)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
10
else
0)
else
(if i.val < 3563 then
27
else
6))
else
(if i.val < 3566 then
(if i.val < 3565 then
0
else
0)
else
(if i.val < 3567 then
19
else
26))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
5
else
29)
else
(if i.val < 3571 then
27
else
9))
else
(if i.val < 3574 then
(if i.val < 3573 then
11
else
35)
else
(if i.val < 3575 then
26
else
12)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
8
else
28)
else
(if i.val < 3579 then
19
else
35))
else
(if i.val < 3582 then
(if i.val < 3581 then
9
else
0)
else
(if i.val < 3583 then
17
else
9)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0007 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
32
else
14)
else
(if i.val < 3587 then
24
else
25))
else
(if i.val < 3590 then
(if i.val < 3589 then
9
else
26)
else
(if i.val < 3591 then
5
else
24)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
6
else
25)
else
(if i.val < 3595 then
9
else
18))
else
(if i.val < 3598 then
(if i.val < 3597 then
30
else
5)
else
(if i.val < 3599 then
14
else
10))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
0
else
27)
else
(if i.val < 3603 then
0
else
19))
else
(if i.val < 3606 then
(if i.val < 3605 then
28
else
0)
else
(if i.val < 3607 then
28
else
0)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
27
else
13)
else
(if i.val < 3611 then
8
else
23))
else
(if i.val < 3614 then
(if i.val < 3613 then
0
else
0)
else
(if i.val < 3615 then
22
else
4)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
29
else
4)
else
(if i.val < 3619 then
21
else
23))
else
(if i.val < 3622 then
(if i.val < 3621 then
23
else
23)
else
(if i.val < 3623 then
23
else
16)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
17
else
35)
else
(if i.val < 3627 then
0
else
20))
else
(if i.val < 3630 then
(if i.val < 3629 then
10
else
23)
else
(if i.val < 3631 then
14
else
23))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
23
else
29)
else
(if i.val < 3635 then
23
else
0))
else
(if i.val < 3638 then
(if i.val < 3637 then
0
else
23)
else
(if i.val < 3639 then
23
else
17)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
4
else
19)
else
(if i.val < 3643 then
4
else
6))
else
(if i.val < 3646 then
(if i.val < 3645 then
4
else
29)
else
(if i.val < 3647 then
0
else
0))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
0
else
0)
else
(if i.val < 3651 then
0
else
0))
else
(if i.val < 3654 then
(if i.val < 3653 then
0
else
0)
else
(if i.val < 3655 then
9
else
10)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
13
else
8)
else
(if i.val < 3659 then
0
else
26))
else
(if i.val < 3662 then
(if i.val < 3661 then
10
else
19)
else
(if i.val < 3663 then
1
else
17))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
14
else
16)
else
(if i.val < 3667 then
18
else
18))
else
(if i.val < 3670 then
(if i.val < 3669 then
28
else
14)
else
(if i.val < 3671 then
9
else
27)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
9
else
28)
else
(if i.val < 3675 then
30
else
0))
else
(if i.val < 3678 then
(if i.val < 3677 then
9
else
28)
else
(if i.val < 3679 then
25
else
23)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
35
else
3)
else
(if i.val < 3683 then
4
else
19))
else
(if i.val < 3686 then
(if i.val < 3685 then
23
else
23)
else
(if i.val < 3687 then
29
else
29)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
33
else
0)
else
(if i.val < 3691 then
29
else
23))
else
(if i.val < 3694 then
(if i.val < 3693 then
24
else
9)
else
(if i.val < 3695 then
23
else
23))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
35
else
23)
else
(if i.val < 3699 then
29
else
29))
else
(if i.val < 3702 then
(if i.val < 3701 then
0
else
0)
else
(if i.val < 3703 then
0
else
0)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
0
else
0)
else
(if i.val < 3707 then
0
else
0))
else
(if i.val < 3710 then
(if i.val < 3709 then
9
else
27)
else
(if i.val < 3711 then
27
else
28)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
11
else
0)
else
(if i.val < 3715 then
14
else
32))
else
(if i.val < 3718 then
(if i.val < 3717 then
28
else
28)
else
(if i.val < 3719 then
13
else
29)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
24
else
27)
else
(if i.val < 3723 then
19
else
33))
else
(if i.val < 3726 then
(if i.val < 3725 then
22
else
6)
else
(if i.val < 3727 then
8
else
0))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
18
else
24)
else
(if i.val < 3731 then
20
else
0))
else
(if i.val < 3734 then
(if i.val < 3733 then
6
else
17)
else
(if i.val < 3735 then
0
else
0)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
6
else
20)
else
(if i.val < 3739 then
14
else
10))
else
(if i.val < 3742 then
(if i.val < 3741 then
11
else
10)
else
(if i.val < 3743 then
10
else
11)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
11
else
13)
else
(if i.val < 3747 then
32
else
33))
else
(if i.val < 3750 then
(if i.val < 3749 then
35
else
21)
else
(if i.val < 3751 then
11
else
0)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
0
else
0)
else
(if i.val < 3755 then
12
else
23))
else
(if i.val < 3758 then
(if i.val < 3757 then
5
else
27)
else
(if i.val < 3759 then
20
else
21))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
24
else
14)
else
(if i.val < 3763 then
24
else
8))
else
(if i.val < 3766 then
(if i.val < 3765 then
8
else
22)
else
(if i.val < 3767 then
11
else
8)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
6
else
10)
else
(if i.val < 3771 then
0
else
8))
else
(if i.val < 3774 then
(if i.val < 3773 then
26
else
20)
else
(if i.val < 3775 then
21
else
5))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
22
else
26)
else
(if i.val < 3779 then
33
else
17))
else
(if i.val < 3782 then
(if i.val < 3781 then
0
else
25)
else
(if i.val < 3783 then
21
else
8)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
21
else
21)
else
(if i.val < 3787 then
22
else
17))
else
(if i.val < 3790 then
(if i.val < 3789 then
33
else
10)
else
(if i.val < 3791 then
0
else
0))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
22
else
0)
else
(if i.val < 3795 then
33
else
26))
else
(if i.val < 3798 then
(if i.val < 3797 then
29
else
8)
else
(if i.val < 3799 then
35
else
10)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
10
else
11)
else
(if i.val < 3803 then
12
else
12))
else
(if i.val < 3806 then
(if i.val < 3805 then
8
else
33)
else
(if i.val < 3807 then
33
else
11)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
10
else
18)
else
(if i.val < 3811 then
33
else
15))
else
(if i.val < 3814 then
(if i.val < 3813 then
12
else
6)
else
(if i.val < 3815 then
0
else
27)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
29
else
0)
else
(if i.val < 3819 then
31
else
1))
else
(if i.val < 3822 then
(if i.val < 3821 then
3
else
11)
else
(if i.val < 3823 then
29
else
13))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
32
else
34)
else
(if i.val < 3827 then
10
else
0))
else
(if i.val < 3830 then
(if i.val < 3829 then
0
else
0)
else
(if i.val < 3831 then
0
else
0)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
0
else
0)
else
(if i.val < 3835 then
7
else
7))
else
(if i.val < 3838 then
(if i.val < 3837 then
6
else
20)
else
(if i.val < 3839 then
1
else
0))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
5
else
7)
else
(if i.val < 3843 then
7
else
7))
else
(if i.val < 3846 then
(if i.val < 3845 then
8
else
25)
else
(if i.val < 3847 then
0
else
4)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
2
else
18)
else
(if i.val < 3851 then
11
else
33))
else
(if i.val < 3854 then
(if i.val < 3853 then
33
else
0)
else
(if i.val < 3855 then
19
else
0))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
5
else
28)
else
(if i.val < 3859 then
22
else
16))
else
(if i.val < 3862 then
(if i.val < 3861 then
25
else
25)
else
(if i.val < 3863 then
27
else
34)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
5
else
27)
else
(if i.val < 3867 then
5
else
25))
else
(if i.val < 3870 then
(if i.val < 3869 then
25
else
0)
else
(if i.val < 3871 then
1
else
4)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
23
else
21)
else
(if i.val < 3875 then
5
else
4))
else
(if i.val < 3878 then
(if i.val < 3877 then
17
else
18)
else
(if i.val < 3879 then
14
else
11)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
11
else
16)
else
(if i.val < 3883 then
5
else
8))
else
(if i.val < 3886 then
(if i.val < 3885 then
13
else
32)
else
(if i.val < 3887 then
14
else
14))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
33
else
4)
else
(if i.val < 3891 then
3
else
35))
else
(if i.val < 3894 then
(if i.val < 3893 then
16
else
0)
else
(if i.val < 3895 then
0
else
0)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
8
else
35)
else
(if i.val < 3899 then
35
else
12))
else
(if i.val < 3902 then
(if i.val < 3901 then
6
else
21)
else
(if i.val < 3903 then
21
else
10))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
34
else
1)
else
(if i.val < 3907 then
8
else
0))
else
(if i.val < 3910 then
(if i.val < 3909 then
0
else
0)
else
(if i.val < 3911 then
0
else
14)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
11
else
0)
else
(if i.val < 3915 then
12
else
28))
else
(if i.val < 3918 then
(if i.val < 3917 then
16
else
25)
else
(if i.val < 3919 then
5
else
32))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
14
else
16)
else
(if i.val < 3923 then
0
else
0))
else
(if i.val < 3926 then
(if i.val < 3925 then
9
else
14)
else
(if i.val < 3927 then
0
else
19)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
21
else
10)
else
(if i.val < 3931 then
35
else
27))
else
(if i.val < 3934 then
(if i.val < 3933 then
10
else
13)
else
(if i.val < 3935 then
12
else
11)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
12
else
11)
else
(if i.val < 3939 then
35
else
18))
else
(if i.val < 3942 then
(if i.val < 3941 then
10
else
31)
else
(if i.val < 3943 then
0
else
0)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
12
else
17)
else
(if i.val < 3947 then
28
else
26))
else
(if i.val < 3950 then
(if i.val < 3949 then
32
else
18)
else
(if i.val < 3951 then
10
else
7))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
5
else
11)
else
(if i.val < 3955 then
11
else
20))
else
(if i.val < 3958 then
(if i.val < 3957 then
15
else
24)
else
(if i.val < 3959 then
32
else
7)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
1
else
0)
else
(if i.val < 3963 then
27
else
35))
else
(if i.val < 3966 then
(if i.val < 3965 then
20
else
18)
else
(if i.val < 3967 then
1
else
11)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
8
else
16)
else
(if i.val < 3971 then
11
else
29))
else
(if i.val < 3974 then
(if i.val < 3973 then
24
else
0)
else
(if i.val < 3975 then
0
else
0)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
0
else
0)
else
(if i.val < 3979 then
0
else
0))
else
(if i.val < 3982 then
(if i.val < 3981 then
0
else
0)
else
(if i.val < 3983 then
0
else
0))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
0
else
0)
else
(if i.val < 3987 then
0
else
0))
else
(if i.val < 3990 then
(if i.val < 3989 then
26
else
29)
else
(if i.val < 3991 then
13
else
4)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
31
else
0)
else
(if i.val < 3995 then
13
else
35))
else
(if i.val < 3998 then
(if i.val < 3997 then
0
else
14)
else
(if i.val < 3999 then
29
else
10)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
8
else
7)
else
(if i.val < 4003 then
12
else
31))
else
(if i.val < 4006 then
(if i.val < 4005 then
30
else
34)
else
(if i.val < 4007 then
15
else
32)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
31
else
9)
else
(if i.val < 4011 then
25
else
12))
else
(if i.val < 4014 then
(if i.val < 4013 then
16
else
23)
else
(if i.val < 4015 then
13
else
22))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
8
else
8)
else
(if i.val < 4019 then
16
else
21))
else
(if i.val < 4022 then
(if i.val < 4021 then
31
else
1)
else
(if i.val < 4023 then
29
else
33)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
29
else
31)
else
(if i.val < 4027 then
19
else
23))
else
(if i.val < 4030 then
(if i.val < 4029 then
34
else
0)
else
(if i.val < 4031 then
13
else
20))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
6
else
29)
else
(if i.val < 4035 then
14
else
23))
else
(if i.val < 4038 then
(if i.val < 4037 then
13
else
8)
else
(if i.val < 4039 then
8
else
25)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
13
else
29)
else
(if i.val < 4043 then
31
else
34))
else
(if i.val < 4046 then
(if i.val < 4045 then
5
else
21)
else
(if i.val < 4047 then
24
else
21))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
5
else
29)
else
(if i.val < 4051 then
3
else
35))
else
(if i.val < 4054 then
(if i.val < 4053 then
21
else
9)
else
(if i.val < 4055 then
33
else
13)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
20
else
24)
else
(if i.val < 4059 then
18
else
5))
else
(if i.val < 4062 then
(if i.val < 4061 then
0
else
20)
else
(if i.val < 4063 then
0
else
0)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
0
else
8)
else
(if i.val < 4067 then
0
else
30))
else
(if i.val < 4070 then
(if i.val < 4069 then
16
else
5)
else
(if i.val < 4071 then
10
else
1)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
17
else
20)
else
(if i.val < 4075 then
0
else
10))
else
(if i.val < 4078 then
(if i.val < 4077 then
6
else
23)
else
(if i.val < 4079 then
0
else
17))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
23
else
32)
else
(if i.val < 4083 then
0
else
19))
else
(if i.val < 4086 then
(if i.val < 4085 then
9
else
8)
else
(if i.val < 4087 then
19
else
23)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
23
else
13)
else
(if i.val < 4091 then
33
else
16))
else
(if i.val < 4094 then
(if i.val < 4093 then
26
else
2)
else
(if i.val < 4095 then
29
else
23)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorFactorColumn3Part0008 : Fin 4320 → Fin 36 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
28
else
(if i.val < 4098 then
1
else
12))
else
(if i.val < 4101 then
(if i.val < 4100 then
9
else
13)
else
(if i.val < 4102 then
14
else
1)))
else
(if i.val < 4106 then
(if i.val < 4104 then
24
else
(if i.val < 4105 then
28
else
30))
else
(if i.val < 4108 then
(if i.val < 4107 then
9
else
35)
else
(if i.val < 4109 then
29
else
29))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
29
else
(if i.val < 4112 then
12
else
30))
else
(if i.val < 4115 then
(if i.val < 4114 then
9
else
4)
else
(if i.val < 4116 then
2
else
29)))
else
(if i.val < 4120 then
(if i.val < 4118 then
30
else
(if i.val < 4119 then
20
else
2))
else
(if i.val < 4122 then
(if i.val < 4121 then
18
else
22)
else
(if i.val < 4123 then
7
else
14)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
35
else
(if i.val < 4126 then
13
else
29))
else
(if i.val < 4129 then
(if i.val < 4128 then
29
else
20)
else
(if i.val < 4130 then
29
else
0)))
else
(if i.val < 4134 then
(if i.val < 4132 then
14
else
(if i.val < 4133 then
3
else
16))
else
(if i.val < 4136 then
(if i.val < 4135 then
9
else
33)
else
(if i.val < 4137 then
28
else
21))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
5
else
(if i.val < 4140 then
4
else
8))
else
(if i.val < 4143 then
(if i.val < 4142 then
27
else
16)
else
(if i.val < 4144 then
1
else
20)))
else
(if i.val < 4148 then
(if i.val < 4146 then
0
else
(if i.val < 4147 then
27
else
20))
else
(if i.val < 4150 then
(if i.val < 4149 then
22
else
17)
else
(if i.val < 4151 then
23
else
33))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
1
else
(if i.val < 4154 then
0
else
19))
else
(if i.val < 4157 then
(if i.val < 4156 then
32
else
29)
else
(if i.val < 4158 then
20
else
25)))
else
(if i.val < 4162 then
(if i.val < 4160 then
22
else
(if i.val < 4161 then
14
else
23))
else
(if i.val < 4164 then
(if i.val < 4163 then
33
else
23)
else
(if i.val < 4165 then
4
else
0))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
23
else
(if i.val < 4168 then
23
else
24))
else
(if i.val < 4171 then
(if i.val < 4170 then
14
else
19)
else
(if i.val < 4172 then
8
else
0)))
else
(if i.val < 4176 then
(if i.val < 4174 then
0
else
(if i.val < 4175 then
33
else
23))
else
(if i.val < 4178 then
(if i.val < 4177 then
12
else
23)
else
(if i.val < 4179 then
0
else
9)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
25
else
(if i.val < 4182 then
6
else
35))
else
(if i.val < 4185 then
(if i.val < 4184 then
0
else
0)
else
(if i.val < 4186 then
0
else
31)))
else
(if i.val < 4190 then
(if i.val < 4188 then
8
else
(if i.val < 4189 then
0
else
0))
else
(if i.val < 4192 then
(if i.val < 4191 then
13
else
26)
else
(if i.val < 4193 then
8
else
32))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
9
else
(if i.val < 4196 then
29
else
18))
else
(if i.val < 4199 then
(if i.val < 4198 then
24
else
4)
else
(if i.val < 4200 then
3
else
29)))
else
(if i.val < 4204 then
(if i.val < 4202 then
13
else
(if i.val < 4203 then
11
else
28))
else
(if i.val < 4206 then
(if i.val < 4205 then
26
else
3)
else
(if i.val < 4207 then
23
else
35)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
3
else
(if i.val < 4210 then
15
else
12))
else
(if i.val < 4213 then
(if i.val < 4212 then
7
else
30)
else
(if i.val < 4214 then
14
else
11)))
else
(if i.val < 4218 then
(if i.val < 4216 then
22
else
(if i.val < 4217 then
17
else
29))
else
(if i.val < 4220 then
(if i.val < 4219 then
0
else
18)
else
(if i.val < 4221 then
24
else
23))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
23
else
(if i.val < 4224 then
21
else
2))
else
(if i.val < 4227 then
(if i.val < 4226 then
5
else
19)
else
(if i.val < 4228 then
0
else
31)))
else
(if i.val < 4232 then
(if i.val < 4230 then
0
else
(if i.val < 4231 then
1
else
28))
else
(if i.val < 4234 then
(if i.val < 4233 then
32
else
8)
else
(if i.val < 4235 then
12
else
2)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
8
else
(if i.val < 4238 then
20
else
20))
else
(if i.val < 4241 then
(if i.val < 4240 then
23
else
27)
else
(if i.val < 4242 then
16
else
12)))
else
(if i.val < 4246 then
(if i.val < 4244 then
28
else
(if i.val < 4245 then
35
else
5))
else
(if i.val < 4248 then
(if i.val < 4247 then
5
else
1)
else
(if i.val < 4249 then
8
else
33))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
8
else
(if i.val < 4252 then
24
else
35))
else
(if i.val < 4255 then
(if i.val < 4254 then
1
else
3)
else
(if i.val < 4256 then
11
else
24)))
else
(if i.val < 4260 then
(if i.val < 4258 then
8
else
(if i.val < 4259 then
11
else
1))
else
(if i.val < 4262 then
(if i.val < 4261 then
28
else
13)
else
(if i.val < 4263 then
15
else
1))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
22
else
(if i.val < 4266 then
0
else
14))
else
(if i.val < 4269 then
(if i.val < 4268 then
27
else
11)
else
(if i.val < 4270 then
11
else
11)))
else
(if i.val < 4274 then
(if i.val < 4272 then
8
else
(if i.val < 4273 then
0
else
0))
else
(if i.val < 4276 then
(if i.val < 4275 then
3
else
34)
else
(if i.val < 4277 then
31
else
0))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
2
else
(if i.val < 4280 then
35
else
12))
else
(if i.val < 4283 then
(if i.val < 4282 then
18
else
6)
else
(if i.val < 4284 then
12
else
11)))
else
(if i.val < 4288 then
(if i.val < 4286 then
7
else
(if i.val < 4287 then
10
else
34))
else
(if i.val < 4290 then
(if i.val < 4289 then
20
else
20)
else
(if i.val < 4291 then
0
else
0)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
0
else
(if i.val < 4294 then
2
else
2))
else
(if i.val < 4297 then
(if i.val < 4296 then
13
else
28)
else
(if i.val < 4298 then
17
else
34)))
else
(if i.val < 4302 then
(if i.val < 4300 then
23
else
(if i.val < 4301 then
33
else
8))
else
(if i.val < 4304 then
(if i.val < 4303 then
0
else
17)
else
(if i.val < 4305 then
23
else
35))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
5
else
(if i.val < 4308 then
5
else
7))
else
(if i.val < 4311 then
(if i.val < 4310 then
20
else
12)
else
(if i.val < 4312 then
23
else
8)))
else
(if i.val < 4316 then
(if i.val < 4314 then
13
else
(if i.val < 4315 then
10
else
26))
else
(if i.val < 4318 then
(if i.val < 4317 then
23
else
12)
else
(if i.val < 4319 then
6
else
22))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0000 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
1
else
5)
else
(if i.val < 3 then
6
else
7))
else
(if i.val < 6 then
(if i.val < 5 then
8
else
0)
else
(if i.val < 7 then
19
else
20)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
21
else
22)
else
(if i.val < 11 then
23
else
24))
else
(if i.val < 14 then
(if i.val < 13 then
25
else
26)
else
(if i.val < 15 then
27
else
28))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
29
else
30)
else
(if i.val < 19 then
31
else
2))
else
(if i.val < 22 then
(if i.val < 21 then
3
else
4)
else
(if i.val < 23 then
59
else
60)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
61
else
62)
else
(if i.val < 27 then
63
else
64))
else
(if i.val < 30 then
(if i.val < 29 then
65
else
66)
else
(if i.val < 31 then
67
else
68)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
69
else
70)
else
(if i.val < 35 then
71
else
72))
else
(if i.val < 38 then
(if i.val < 37 then
73
else
74)
else
(if i.val < 39 then
75
else
76)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
77
else
78)
else
(if i.val < 43 then
79
else
80))
else
(if i.val < 46 then
(if i.val < 45 then
81
else
82)
else
(if i.val < 47 then
83
else
84))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
85
else
86)
else
(if i.val < 51 then
87
else
88))
else
(if i.val < 54 then
(if i.val < 53 then
89
else
90)
else
(if i.val < 55 then
91
else
92)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
93
else
94)
else
(if i.val < 59 then
95
else
9))
else
(if i.val < 62 then
(if i.val < 61 then
10
else
11)
else
(if i.val < 63 then
12
else
13))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
14
else
15)
else
(if i.val < 67 then
16
else
17))
else
(if i.val < 70 then
(if i.val < 69 then
18
else
163)
else
(if i.val < 71 then
164
else
165)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
166
else
167)
else
(if i.val < 75 then
168
else
169))
else
(if i.val < 78 then
(if i.val < 77 then
170
else
171)
else
(if i.val < 79 then
172
else
173))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
174
else
175)
else
(if i.val < 83 then
176
else
177))
else
(if i.val < 86 then
(if i.val < 85 then
178
else
179)
else
(if i.val < 87 then
180
else
181)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
182
else
183)
else
(if i.val < 91 then
184
else
185))
else
(if i.val < 94 then
(if i.val < 93 then
186
else
187)
else
(if i.val < 95 then
188
else
189)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
190
else
191)
else
(if i.val < 99 then
192
else
193))
else
(if i.val < 102 then
(if i.val < 101 then
194
else
195)
else
(if i.val < 103 then
196
else
197)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
125
else
198)
else
(if i.val < 107 then
199
else
200))
else
(if i.val < 110 then
(if i.val < 109 then
201
else
202)
else
(if i.val < 111 then
203
else
204))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
205
else
206)
else
(if i.val < 115 then
207
else
208))
else
(if i.val < 118 then
(if i.val < 117 then
209
else
210)
else
(if i.val < 119 then
211
else
212)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
213
else
214)
else
(if i.val < 123 then
215
else
216))
else
(if i.val < 126 then
(if i.val < 125 then
217
else
218)
else
(if i.val < 127 then
219
else
220)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
221
else
222)
else
(if i.val < 131 then
223
else
224))
else
(if i.val < 134 then
(if i.val < 133 then
225
else
226)
else
(if i.val < 135 then
227
else
228)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
229
else
230)
else
(if i.val < 139 then
231
else
232))
else
(if i.val < 142 then
(if i.val < 141 then
233
else
234)
else
(if i.val < 143 then
235
else
236))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
237
else
238)
else
(if i.val < 147 then
239
else
240))
else
(if i.val < 150 then
(if i.val < 149 then
241
else
242)
else
(if i.val < 151 then
243
else
244)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
245
else
246)
else
(if i.val < 155 then
247
else
248))
else
(if i.val < 158 then
(if i.val < 157 then
249
else
250)
else
(if i.val < 159 then
97
else
251)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
252
else
253)
else
(if i.val < 163 then
254
else
32))
else
(if i.val < 166 then
(if i.val < 165 then
33
else
34)
else
(if i.val < 167 then
35
else
36)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
37
else
38)
else
(if i.val < 171 then
39
else
40))
else
(if i.val < 174 then
(if i.val < 173 then
41
else
42)
else
(if i.val < 175 then
43
else
44))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
45
else
46)
else
(if i.val < 179 then
47
else
48))
else
(if i.val < 182 then
(if i.val < 181 then
49
else
50)
else
(if i.val < 183 then
51
else
52)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
53
else
54)
else
(if i.val < 187 then
55
else
56))
else
(if i.val < 190 then
(if i.val < 189 then
57
else
58)
else
(if i.val < 191 then
400
else
158))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
401
else
402)
else
(if i.val < 195 then
403
else
404))
else
(if i.val < 198 then
(if i.val < 197 then
405
else
406)
else
(if i.val < 199 then
407
else
408)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
409
else
410)
else
(if i.val < 203 then
411
else
412))
else
(if i.val < 206 then
(if i.val < 205 then
413
else
339)
else
(if i.val < 207 then
414
else
415))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
416
else
417)
else
(if i.val < 211 then
418
else
419))
else
(if i.val < 214 then
(if i.val < 213 then
420
else
421)
else
(if i.val < 215 then
422
else
423)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
424
else
425)
else
(if i.val < 219 then
104
else
426))
else
(if i.val < 222 then
(if i.val < 221 then
427
else
428)
else
(if i.val < 223 then
429
else
430)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
431
else
432)
else
(if i.val < 227 then
433
else
434))
else
(if i.val < 230 then
(if i.val < 229 then
317
else
435)
else
(if i.val < 231 then
436
else
437)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
315
else
438)
else
(if i.val < 235 then
439
else
440))
else
(if i.val < 238 then
(if i.val < 237 then
441
else
442)
else
(if i.val < 239 then
443
else
444))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
445
else
446)
else
(if i.val < 243 then
447
else
448))
else
(if i.val < 246 then
(if i.val < 245 then
449
else
450)
else
(if i.val < 247 then
451
else
452)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
453
else
454)
else
(if i.val < 251 then
455
else
456))
else
(if i.val < 254 then
(if i.val < 253 then
457
else
458)
else
(if i.val < 255 then
459
else
460))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
461
else
462)
else
(if i.val < 259 then
463
else
464))
else
(if i.val < 262 then
(if i.val < 261 then
465
else
466)
else
(if i.val < 263 then
467
else
468)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
469
else
470)
else
(if i.val < 267 then
471
else
472))
else
(if i.val < 270 then
(if i.val < 269 then
473
else
474)
else
(if i.val < 271 then
475
else
476))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
477
else
478)
else
(if i.val < 275 then
479
else
480))
else
(if i.val < 278 then
(if i.val < 277 then
481
else
482)
else
(if i.val < 279 then
483
else
484)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
289
else
485)
else
(if i.val < 283 then
486
else
487))
else
(if i.val < 286 then
(if i.val < 285 then
488
else
489)
else
(if i.val < 287 then
490
else
491)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
323
else
492)
else
(if i.val < 291 then
493
else
494))
else
(if i.val < 294 then
(if i.val < 293 then
495
else
496)
else
(if i.val < 295 then
497
else
498)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
499
else
500)
else
(if i.val < 299 then
501
else
502))
else
(if i.val < 302 then
(if i.val < 301 then
503
else
504)
else
(if i.val < 303 then
505
else
506))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
507
else
508)
else
(if i.val < 307 then
509
else
510))
else
(if i.val < 310 then
(if i.val < 309 then
511
else
512)
else
(if i.val < 311 then
513
else
514)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
515
else
516)
else
(if i.val < 315 then
517
else
139))
else
(if i.val < 318 then
(if i.val < 317 then
518
else
135)
else
(if i.val < 319 then
519
else
520))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
521
else
522)
else
(if i.val < 323 then
256
else
523))
else
(if i.val < 326 then
(if i.val < 325 then
524
else
525)
else
(if i.val < 327 then
526
else
527)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
528
else
529)
else
(if i.val < 331 then
530
else
341))
else
(if i.val < 334 then
(if i.val < 333 then
531
else
532)
else
(if i.val < 335 then
533
else
534))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
535
else
536)
else
(if i.val < 339 then
537
else
112))
else
(if i.val < 342 then
(if i.val < 341 then
538
else
539)
else
(if i.val < 343 then
540
else
541)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
542
else
318)
else
(if i.val < 347 then
543
else
544))
else
(if i.val < 350 then
(if i.val < 349 then
545
else
546)
else
(if i.val < 351 then
547
else
548)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
549
else
550)
else
(if i.val < 355 then
551
else
552))
else
(if i.val < 358 then
(if i.val < 357 then
553
else
554)
else
(if i.val < 359 then
555
else
556)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
557
else
558)
else
(if i.val < 363 then
559
else
560))
else
(if i.val < 366 then
(if i.val < 365 then
561
else
327)
else
(if i.val < 367 then
562
else
563))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
564
else
565)
else
(if i.val < 371 then
566
else
567))
else
(if i.val < 374 then
(if i.val < 373 then
568
else
569)
else
(if i.val < 375 then
570
else
571)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
572
else
573)
else
(if i.val < 379 then
574
else
575))
else
(if i.val < 382 then
(if i.val < 381 then
576
else
577)
else
(if i.val < 383 then
578
else
579)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
580
else
581)
else
(if i.val < 387 then
582
else
583))
else
(if i.val < 390 then
(if i.val < 389 then
584
else
585)
else
(if i.val < 391 then
586
else
587)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
588
else
589)
else
(if i.val < 395 then
590
else
591))
else
(if i.val < 398 then
(if i.val < 397 then
592
else
593)
else
(if i.val < 399 then
594
else
595))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
96
else
98)
else
(if i.val < 403 then
99
else
100))
else
(if i.val < 406 then
(if i.val < 405 then
101
else
102)
else
(if i.val < 407 then
103
else
105)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
106
else
107)
else
(if i.val < 411 then
108
else
109))
else
(if i.val < 414 then
(if i.val < 413 then
110
else
111)
else
(if i.val < 415 then
113
else
114)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
115
else
116)
else
(if i.val < 419 then
117
else
118))
else
(if i.val < 422 then
(if i.val < 421 then
119
else
120)
else
(if i.val < 423 then
121
else
122)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
123
else
124)
else
(if i.val < 427 then
126
else
127))
else
(if i.val < 430 then
(if i.val < 429 then
128
else
129)
else
(if i.val < 431 then
130
else
131))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
132
else
133)
else
(if i.val < 435 then
134
else
136))
else
(if i.val < 438 then
(if i.val < 437 then
137
else
138)
else
(if i.val < 439 then
140
else
141)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
142
else
143)
else
(if i.val < 443 then
144
else
145))
else
(if i.val < 446 then
(if i.val < 445 then
146
else
147)
else
(if i.val < 447 then
148
else
149))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
150
else
151)
else
(if i.val < 451 then
152
else
153))
else
(if i.val < 454 then
(if i.val < 453 then
154
else
155)
else
(if i.val < 455 then
156
else
157)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
159
else
160)
else
(if i.val < 459 then
161
else
162))
else
(if i.val < 462 then
(if i.val < 461 then
899
else
322)
else
(if i.val < 463 then
900
else
901))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
902
else
903)
else
(if i.val < 467 then
904
else
905))
else
(if i.val < 470 then
(if i.val < 469 then
906
else
907)
else
(if i.val < 471 then
908
else
909)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
910
else
911)
else
(if i.val < 475 then
683
else
912))
else
(if i.val < 478 then
(if i.val < 477 then
913
else
914)
else
(if i.val < 479 then
915
else
916)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
917
else
918)
else
(if i.val < 483 then
919
else
920))
else
(if i.val < 486 then
(if i.val < 485 then
921
else
922)
else
(if i.val < 487 then
923
else
924)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
925
else
926)
else
(if i.val < 491 then
927
else
754))
else
(if i.val < 494 then
(if i.val < 493 then
280
else
928)
else
(if i.val < 495 then
929
else
930))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
772
else
931)
else
(if i.val < 499 then
932
else
933))
else
(if i.val < 502 then
(if i.val < 501 then
934
else
935)
else
(if i.val < 503 then
936
else
937)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
938
else
634)
else
(if i.val < 507 then
939
else
940))
else
(if i.val < 510 then
(if i.val < 509 then
717
else
632)
else
(if i.val < 511 then
941
else
942)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0001 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
943
else
944)
else
(if i.val < 515 then
945
else
946))
else
(if i.val < 518 then
(if i.val < 517 then
947
else
948)
else
(if i.val < 519 then
949
else
345)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
728
else
950)
else
(if i.val < 523 then
951
else
288))
else
(if i.val < 526 then
(if i.val < 525 then
952
else
953)
else
(if i.val < 527 then
954
else
365))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
955
else
956)
else
(if i.val < 531 then
957
else
958))
else
(if i.val < 534 then
(if i.val < 533 then
959
else
960)
else
(if i.val < 535 then
961
else
787)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
962
else
963)
else
(if i.val < 539 then
964
else
331))
else
(if i.val < 542 then
(if i.val < 541 then
965
else
966)
else
(if i.val < 543 then
716
else
735)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
967
else
968)
else
(if i.val < 547 then
969
else
970))
else
(if i.val < 550 then
(if i.val < 549 then
971
else
734)
else
(if i.val < 551 then
731
else
972)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
973
else
974)
else
(if i.val < 555 then
975
else
976))
else
(if i.val < 558 then
(if i.val < 557 then
977
else
978)
else
(if i.val < 559 then
979
else
980))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
981
else
982)
else
(if i.val < 563 then
983
else
984))
else
(if i.val < 566 then
(if i.val < 565 then
985
else
986)
else
(if i.val < 567 then
987
else
988)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
989
else
990)
else
(if i.val < 571 then
991
else
992))
else
(if i.val < 574 then
(if i.val < 573 then
993
else
994)
else
(if i.val < 575 then
995
else
996))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
997
else
998)
else
(if i.val < 579 then
999
else
1000))
else
(if i.val < 582 then
(if i.val < 581 then
1001
else
1002)
else
(if i.val < 583 then
1003
else
1004)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1005
else
733)
else
(if i.val < 587 then
1006
else
1007))
else
(if i.val < 590 then
(if i.val < 589 then
1008
else
1009)
else
(if i.val < 591 then
1010
else
1011))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1012
else
1013)
else
(if i.val < 595 then
771
else
1014))
else
(if i.val < 598 then
(if i.val < 597 then
1015
else
1016)
else
(if i.val < 599 then
1017
else
1018)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1019
else
1020)
else
(if i.val < 603 then
1021
else
1022))
else
(if i.val < 606 then
(if i.val < 605 then
1023
else
864)
else
(if i.val < 607 then
1024
else
1025)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1026
else
1027)
else
(if i.val < 611 then
1028
else
1029))
else
(if i.val < 614 then
(if i.val < 613 then
1030
else
1031)
else
(if i.val < 615 then
1032
else
1033)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1034
else
1035)
else
(if i.val < 619 then
1036
else
1037))
else
(if i.val < 622 then
(if i.val < 621 then
1038
else
1039)
else
(if i.val < 623 then
1040
else
1041))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1042
else
1043)
else
(if i.val < 627 then
1044
else
1045))
else
(if i.val < 630 then
(if i.val < 629 then
1046
else
1047)
else
(if i.val < 631 then
603
else
1048)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
306
else
1049)
else
(if i.val < 635 then
302
else
1050))
else
(if i.val < 638 then
(if i.val < 637 then
1051
else
826)
else
(if i.val < 639 then
1052
else
1053)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
1054
else
1055)
else
(if i.val < 643 then
1056
else
1057))
else
(if i.val < 646 then
(if i.val < 645 then
1058
else
819)
else
(if i.val < 647 then
1059
else
1060)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
1061
else
1062)
else
(if i.val < 651 then
1063
else
639))
else
(if i.val < 654 then
(if i.val < 653 then
1064
else
1065)
else
(if i.val < 655 then
1066
else
1067))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
1068
else
1069)
else
(if i.val < 659 then
1070
else
1071))
else
(if i.val < 662 then
(if i.val < 661 then
848
else
1072)
else
(if i.val < 663 then
1073
else
1074)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
1075
else
1076)
else
(if i.val < 667 then
1077
else
1078))
else
(if i.val < 670 then
(if i.val < 669 then
1079
else
1080)
else
(if i.val < 671 then
1081
else
1082)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
1083
else
1084)
else
(if i.val < 675 then
1085
else
843))
else
(if i.val < 678 then
(if i.val < 677 then
1086
else
1087)
else
(if i.val < 679 then
1088
else
1089)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
1090
else
1091)
else
(if i.val < 683 then
1092
else
269))
else
(if i.val < 686 then
(if i.val < 685 then
1093
else
788)
else
(if i.val < 687 then
1094
else
1095))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1096
else
1097)
else
(if i.val < 691 then
1098
else
1099))
else
(if i.val < 694 then
(if i.val < 693 then
1100
else
1101)
else
(if i.val < 695 then
1102
else
1103)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1104
else
1105)
else
(if i.val < 699 then
1106
else
1107))
else
(if i.val < 702 then
(if i.val < 701 then
1108
else
1109)
else
(if i.val < 703 then
1110
else
1111))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1112
else
1113)
else
(if i.val < 707 then
1114
else
1115))
else
(if i.val < 710 then
(if i.val < 709 then
1116
else
1117)
else
(if i.val < 711 then
1118
else
1119)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1120
else
1121)
else
(if i.val < 715 then
1122
else
1123))
else
(if i.val < 718 then
(if i.val < 717 then
344
else
305)
else
(if i.val < 719 then
1124
else
1125))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
1126
else
1127)
else
(if i.val < 723 then
1128
else
1129))
else
(if i.val < 726 then
(if i.val < 725 then
1130
else
1131)
else
(if i.val < 727 then
1132
else
1133)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
319
else
1134)
else
(if i.val < 731 then
1135
else
353))
else
(if i.val < 734 then
(if i.val < 733 then
1136
else
389)
else
(if i.val < 735 then
352
else
346)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1137
else
1138)
else
(if i.val < 739 then
769
else
1139))
else
(if i.val < 742 then
(if i.val < 741 then
773
else
1140)
else
(if i.val < 743 then
1141
else
1142)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
1143
else
1144)
else
(if i.val < 747 then
1145
else
1146))
else
(if i.val < 750 then
(if i.val < 749 then
1147
else
1148)
else
(if i.val < 751 then
1149
else
1150))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1151
else
1152)
else
(if i.val < 755 then
287
else
1153))
else
(if i.val < 758 then
(if i.val < 757 then
1154
else
1155)
else
(if i.val < 759 then
1156
else
1157)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1158
else
1159)
else
(if i.val < 763 then
766
else
1160))
else
(if i.val < 766 then
(if i.val < 765 then
1161
else
776)
else
(if i.val < 767 then
1162
else
1163))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1164
else
1165)
else
(if i.val < 771 then
1166
else
398))
else
(if i.val < 774 then
(if i.val < 773 then
293
else
1167)
else
(if i.val < 775 then
1168
else
750)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1169
else
1170)
else
(if i.val < 779 then
1171
else
1172))
else
(if i.val < 782 then
(if i.val < 781 then
1173
else
1174)
else
(if i.val < 783 then
1175
else
789))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1176
else
1177)
else
(if i.val < 787 then
1178
else
336))
else
(if i.val < 790 then
(if i.val < 789 then
1179
else
1180)
else
(if i.val < 791 then
1181
else
1182)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1183
else
736)
else
(if i.val < 795 then
1184
else
1185))
else
(if i.val < 798 then
(if i.val < 797 then
1186
else
1187)
else
(if i.val < 799 then
1188
else
1189)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1190
else
1191)
else
(if i.val < 803 then
780
else
1192))
else
(if i.val < 806 then
(if i.val < 805 then
1193
else
1194)
else
(if i.val < 807 then
1195
else
613)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
1196
else
1197)
else
(if i.val < 811 then
1198
else
1199))
else
(if i.val < 814 then
(if i.val < 813 then
1200
else
1201)
else
(if i.val < 815 then
1202
else
1203))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1204
else
1205)
else
(if i.val < 819 then
1206
else
1207))
else
(if i.val < 822 then
(if i.val < 821 then
1208
else
1209)
else
(if i.val < 823 then
1210
else
1211)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
640
else
1212)
else
(if i.val < 827 then
1213
else
1214))
else
(if i.val < 830 then
(if i.val < 829 then
1215
else
1216)
else
(if i.val < 831 then
1217
else
1218))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
1219
else
1220)
else
(if i.val < 835 then
1221
else
1222))
else
(if i.val < 838 then
(if i.val < 837 then
1223
else
1224)
else
(if i.val < 839 then
616
else
1225)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1226
else
1227)
else
(if i.val < 843 then
1228
else
1229))
else
(if i.val < 846 then
(if i.val < 845 then
1230
else
1231)
else
(if i.val < 847 then
1232
else
1233))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1234
else
1235)
else
(if i.val < 851 then
1236
else
1237))
else
(if i.val < 854 then
(if i.val < 853 then
1238
else
1239)
else
(if i.val < 855 then
1240
else
673)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1241
else
1242)
else
(if i.val < 859 then
1243
else
1244))
else
(if i.val < 862 then
(if i.val < 861 then
1245
else
1246)
else
(if i.val < 863 then
1247
else
1248)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
1249
else
1250)
else
(if i.val < 867 then
1251
else
1252))
else
(if i.val < 870 then
(if i.val < 869 then
1253
else
1254)
else
(if i.val < 871 then
1255
else
1256)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1257
else
1258)
else
(if i.val < 875 then
1259
else
1260))
else
(if i.val < 878 then
(if i.val < 877 then
1261
else
1262)
else
(if i.val < 879 then
1263
else
1264))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1265
else
1266)
else
(if i.val < 883 then
1267
else
604))
else
(if i.val < 886 then
(if i.val < 885 then
1268
else
1269)
else
(if i.val < 887 then
1270
else
1271)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1272
else
749)
else
(if i.val < 891 then
1273
else
1274))
else
(if i.val < 894 then
(if i.val < 893 then
1275
else
1276)
else
(if i.val < 895 then
1277
else
1278)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1279
else
1280)
else
(if i.val < 899 then
1281
else
255))
else
(if i.val < 902 then
(if i.val < 901 then
257
else
258)
else
(if i.val < 903 then
259
else
260)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
261
else
262)
else
(if i.val < 907 then
263
else
264))
else
(if i.val < 910 then
(if i.val < 909 then
265
else
266)
else
(if i.val < 911 then
267
else
268))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
270
else
271)
else
(if i.val < 915 then
272
else
273))
else
(if i.val < 918 then
(if i.val < 917 then
274
else
275)
else
(if i.val < 919 then
276
else
277)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
278
else
279)
else
(if i.val < 923 then
281
else
282))
else
(if i.val < 926 then
(if i.val < 925 then
283
else
284)
else
(if i.val < 927 then
285
else
286)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
290
else
291)
else
(if i.val < 931 then
292
else
294))
else
(if i.val < 934 then
(if i.val < 933 then
295
else
296)
else
(if i.val < 935 then
297
else
298)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
299
else
300)
else
(if i.val < 939 then
301
else
303))
else
(if i.val < 942 then
(if i.val < 941 then
304
else
307)
else
(if i.val < 943 then
308
else
309))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
310
else
311)
else
(if i.val < 947 then
312
else
313))
else
(if i.val < 950 then
(if i.val < 949 then
314
else
316)
else
(if i.val < 951 then
320
else
321)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
324
else
325)
else
(if i.val < 955 then
326
else
328))
else
(if i.val < 958 then
(if i.val < 957 then
329
else
330)
else
(if i.val < 959 then
332
else
333))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
334
else
335)
else
(if i.val < 963 then
337
else
338))
else
(if i.val < 966 then
(if i.val < 965 then
340
else
342)
else
(if i.val < 967 then
343
else
347)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
348
else
349)
else
(if i.val < 971 then
350
else
351))
else
(if i.val < 974 then
(if i.val < 973 then
354
else
355)
else
(if i.val < 975 then
356
else
357))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
358
else
359)
else
(if i.val < 979 then
360
else
361))
else
(if i.val < 982 then
(if i.val < 981 then
362
else
363)
else
(if i.val < 983 then
364
else
366)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
367
else
368)
else
(if i.val < 987 then
369
else
370))
else
(if i.val < 990 then
(if i.val < 989 then
371
else
372)
else
(if i.val < 991 then
373
else
374)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
375
else
376)
else
(if i.val < 995 then
377
else
378))
else
(if i.val < 998 then
(if i.val < 997 then
379
else
380)
else
(if i.val < 999 then
381
else
382)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
383
else
384)
else
(if i.val < 1003 then
385
else
386))
else
(if i.val < 1006 then
(if i.val < 1005 then
387
else
388)
else
(if i.val < 1007 then
390
else
391))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
392
else
393)
else
(if i.val < 1011 then
394
else
395))
else
(if i.val < 1014 then
(if i.val < 1013 then
396
else
397)
else
(if i.val < 1015 then
399
else
1803)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
1804
else
1805)
else
(if i.val < 1019 then
1806
else
1807))
else
(if i.val < 1022 then
(if i.val < 1021 then
1808
else
1809)
else
(if i.val < 1023 then
630
else
883)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0002 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
1810
else
1811)
else
(if i.val < 1027 then
1812
else
1813))
else
(if i.val < 1030 then
(if i.val < 1029 then
1814
else
1815)
else
(if i.val < 1031 then
1816
else
807)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
1817
else
1528)
else
(if i.val < 1035 then
838
else
1818))
else
(if i.val < 1038 then
(if i.val < 1037 then
1819
else
1820)
else
(if i.val < 1039 then
1821
else
1822))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
1823
else
1824)
else
(if i.val < 1043 then
1825
else
1826))
else
(if i.val < 1046 then
(if i.val < 1045 then
1827
else
1828)
else
(if i.val < 1047 then
1829
else
1830)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
1523
else
1831)
else
(if i.val < 1051 then
1832
else
1833))
else
(if i.val < 1054 then
(if i.val < 1053 then
1834
else
651)
else
(if i.val < 1055 then
824
else
1483)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
1296
else
1835)
else
(if i.val < 1059 then
1836
else
1837))
else
(if i.val < 1062 then
(if i.val < 1061 then
1838
else
1839)
else
(if i.val < 1063 then
1840
else
1454)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
1841
else
1842)
else
(if i.val < 1067 then
1843
else
1469))
else
(if i.val < 1070 then
(if i.val < 1069 then
1844
else
1845)
else
(if i.val < 1071 then
1846
else
1847))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
1848
else
1567)
else
(if i.val < 1075 then
1849
else
1311))
else
(if i.val < 1078 then
(if i.val < 1077 then
1850
else
1851)
else
(if i.val < 1079 then
1344
else
1309)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
1852
else
1853)
else
(if i.val < 1083 then
1854
else
1591))
else
(if i.val < 1086 then
(if i.val < 1085 then
855
else
1568)
else
(if i.val < 1087 then
1855
else
1856))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
1857
else
1858)
else
(if i.val < 1091 then
1352
else
1859))
else
(if i.val < 1094 then
(if i.val < 1093 then
1860
else
1602)
else
(if i.val < 1095 then
1861
else
1862)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
1863
else
1864)
else
(if i.val < 1099 then
1865
else
1866))
else
(if i.val < 1102 then
(if i.val < 1101 then
1867
else
1868)
else
(if i.val < 1103 then
1869
else
1870))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
1871
else
1872)
else
(if i.val < 1107 then
1873
else
1874))
else
(if i.val < 1110 then
(if i.val < 1109 then
1875
else
1876)
else
(if i.val < 1111 then
1343
else
1360)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
1358
else
1877)
else
(if i.val < 1115 then
1878
else
1879))
else
(if i.val < 1118 then
(if i.val < 1117 then
1880
else
1881)
else
(if i.val < 1119 then
1357
else
1355)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
1882
else
1883)
else
(if i.val < 1123 then
1884
else
1885))
else
(if i.val < 1126 then
(if i.val < 1125 then
1886
else
1733)
else
(if i.val < 1127 then
1887
else
1888)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
1889
else
1890)
else
(if i.val < 1131 then
1891
else
1892))
else
(if i.val < 1134 then
(if i.val < 1133 then
1491
else
1893)
else
(if i.val < 1135 then
1894
else
1895))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
1896
else
793)
else
(if i.val < 1139 then
1897
else
1356))
else
(if i.val < 1142 then
(if i.val < 1141 then
1898
else
1899)
else
(if i.val < 1143 then
1900
else
1901)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
1902
else
1903)
else
(if i.val < 1147 then
1438
else
1904))
else
(if i.val < 1150 then
(if i.val < 1149 then
889
else
775)
else
(if i.val < 1151 then
1905
else
1599)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
1906
else
1907)
else
(if i.val < 1155 then
1908
else
1493))
else
(if i.val < 1158 then
(if i.val < 1157 then
1909
else
1910)
else
(if i.val < 1159 then
1542
else
1911)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
1912
else
1616)
else
(if i.val < 1163 then
762
else
1913))
else
(if i.val < 1166 then
(if i.val < 1165 then
1914
else
738)
else
(if i.val < 1167 then
1915
else
740))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
1916
else
765)
else
(if i.val < 1171 then
1917
else
1918))
else
(if i.val < 1174 then
(if i.val < 1173 then
1919
else
802)
else
(if i.val < 1175 then
1920
else
1506)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
1541
else
1921)
else
(if i.val < 1179 then
1922
else
685))
else
(if i.val < 1182 then
(if i.val < 1181 then
783
else
1537)
else
(if i.val < 1183 then
1923
else
1924)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
1925
else
1926)
else
(if i.val < 1187 then
1927
else
1928))
else
(if i.val < 1190 then
(if i.val < 1189 then
1929
else
1930)
else
(if i.val < 1191 then
1931
else
1932)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
1522
else
1532)
else
(if i.val < 1195 then
1533
else
1529))
else
(if i.val < 1198 then
(if i.val < 1197 then
1933
else
1934)
else
(if i.val < 1199 then
1935
else
1765))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
1936
else
1937)
else
(if i.val < 1203 then
1938
else
1939))
else
(if i.val < 1206 then
(if i.val < 1205 then
1940
else
1941)
else
(if i.val < 1207 then
1942
else
645)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
1943
else
1944)
else
(if i.val < 1211 then
1945
else
1946))
else
(if i.val < 1214 then
(if i.val < 1213 then
1947
else
637)
else
(if i.val < 1215 then
1948
else
1949))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
1950
else
1951)
else
(if i.val < 1219 then
1952
else
1953))
else
(if i.val < 1222 then
(if i.val < 1221 then
1624
else
1954)
else
(if i.val < 1223 then
1955
else
1956)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
1957
else
1958)
else
(if i.val < 1227 then
1959
else
1960))
else
(if i.val < 1230 then
(if i.val < 1229 then
1961
else
675)
else
(if i.val < 1231 then
1962
else
1615))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
1963
else
1964)
else
(if i.val < 1235 then
660
else
1774))
else
(if i.val < 1238 then
(if i.val < 1237 then
1681
else
1965)
else
(if i.val < 1239 then
1966
else
1967)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
1968
else
1969)
else
(if i.val < 1243 then
1970
else
1971))
else
(if i.val < 1246 then
(if i.val < 1245 then
1972
else
1973)
else
(if i.val < 1247 then
1974
else
1975)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
1307
else
605)
else
(if i.val < 1251 then
1976
else
1977))
else
(if i.val < 1254 then
(if i.val < 1253 then
1978
else
1979)
else
(if i.val < 1255 then
1980
else
1981)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
1982
else
1983)
else
(if i.val < 1259 then
1984
else
1985))
else
(if i.val < 1262 then
(if i.val < 1261 then
1986
else
1987)
else
(if i.val < 1263 then
1988
else
1989))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
1535
else
1536)
else
(if i.val < 1267 then
1990
else
1991))
else
(if i.val < 1270 then
(if i.val < 1269 then
1992
else
1993)
else
(if i.val < 1271 then
1596
else
1994)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
1692
else
1662)
else
(if i.val < 1275 then
1995
else
1996))
else
(if i.val < 1278 then
(if i.val < 1277 then
1997
else
1998)
else
(if i.val < 1279 then
1593
else
1604))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
1999
else
1531)
else
(if i.val < 1283 then
2000
else
2001))
else
(if i.val < 1286 then
(if i.val < 1285 then
2002
else
2003)
else
(if i.val < 1287 then
2004
else
2005)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
2006
else
2007)
else
(if i.val < 1291 then
2008
else
2009))
else
(if i.val < 1294 then
(if i.val < 1293 then
2010
else
2011)
else
(if i.val < 1295 then
2012
else
2013))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
642
else
2014)
else
(if i.val < 1299 then
2015
else
2016))
else
(if i.val < 1302 then
(if i.val < 1301 then
2017
else
2018)
else
(if i.val < 1303 then
2019
else
1752)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
1747
else
2020)
else
(if i.val < 1307 then
2021
else
863))
else
(if i.val < 1310 then
(if i.val < 1309 then
2022
else
668)
else
(if i.val < 1311 then
2023
else
664)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
2024
else
1510)
else
(if i.val < 1315 then
1750
else
2025))
else
(if i.val < 1318 then
(if i.val < 1317 then
2026
else
2027)
else
(if i.val < 1319 then
2028
else
2029)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
2030
else
2031)
else
(if i.val < 1323 then
2032
else
2033))
else
(if i.val < 1326 then
(if i.val < 1325 then
2034
else
2035)
else
(if i.val < 1327 then
2036
else
2037))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
2038
else
2039)
else
(if i.val < 1331 then
2040
else
2041))
else
(if i.val < 1334 then
(if i.val < 1333 then
2042
else
2043)
else
(if i.val < 1335 then
2044
else
2045)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
2046
else
1298)
else
(if i.val < 1339 then
2047
else
2048))
else
(if i.val < 1342 then
(if i.val < 1341 then
2049
else
2050)
else
(if i.val < 1343 then
2051
else
702))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
667
else
2052)
else
(if i.val < 1347 then
2053
else
2054))
else
(if i.val < 1350 then
(if i.val < 1349 then
2055
else
2056)
else
(if i.val < 1351 then
2057
else
2058)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
680
else
2059)
else
(if i.val < 1355 then
2060
else
711))
else
(if i.val < 1358 then
(if i.val < 1357 then
739
else
710)
else
(if i.val < 1359 then
704
else
1797))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
703
else
1331)
else
(if i.val < 1363 then
2061
else
1693))
else
(if i.val < 1366 then
(if i.val < 1365 then
1466
else
1470)
else
(if i.val < 1367 then
1359
else
2062)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
2063
else
2064)
else
(if i.val < 1371 then
2065
else
2066))
else
(if i.val < 1374 then
(if i.val < 1373 then
2067
else
2068)
else
(if i.val < 1375 then
1722
else
2069)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
2070
else
2071)
else
(if i.val < 1379 then
1676
else
2072))
else
(if i.val < 1382 then
(if i.val < 1381 then
1728
else
1783)
else
(if i.val < 1383 then
2073
else
2074)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
1725
else
2075)
else
(if i.val < 1387 then
2076
else
2077))
else
(if i.val < 1390 then
(if i.val < 1389 then
2078
else
2079)
else
(if i.val < 1391 then
2080
else
2081))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
1432
else
2082)
else
(if i.val < 1395 then
1285
else
2083))
else
(if i.val < 1398 then
(if i.val < 1397 then
2084
else
2085)
else
(if i.val < 1399 then
2086
else
2087)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
2088
else
2089)
else
(if i.val < 1403 then
2090
else
2091))
else
(if i.val < 1406 then
(if i.val < 1405 then
2092
else
2093)
else
(if i.val < 1407 then
2094
else
2095)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
2096
else
1720)
else
(if i.val < 1411 then
1658
else
2097))
else
(if i.val < 1414 then
(if i.val < 1413 then
2098
else
1782)
else
(if i.val < 1415 then
2099
else
2100)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
2101
else
1721)
else
(if i.val < 1419 then
2102
else
2103))
else
(if i.val < 1422 then
(if i.val < 1421 then
2104
else
1455)
else
(if i.val < 1423 then
2105
else
2106))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
2107
else
1724)
else
(if i.val < 1427 then
1548
else
2108))
else
(if i.val < 1430 then
(if i.val < 1429 then
2109
else
2110)
else
(if i.val < 1431 then
2111
else
2112)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
1534
else
2113)
else
(if i.val < 1435 then
2114
else
1677))
else
(if i.val < 1438 then
(if i.val < 1437 then
2115
else
2116)
else
(if i.val < 1439 then
747
else
2117)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
2118
else
2119)
else
(if i.val < 1443 then
2120
else
2121))
else
(if i.val < 1446 then
(if i.val < 1445 then
2122
else
2123)
else
(if i.val < 1447 then
1719
else
2124)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
2125
else
2126)
else
(if i.val < 1451 then
2127
else
1671))
else
(if i.val < 1454 then
(if i.val < 1453 then
2128
else
2129)
else
(if i.val < 1455 then
650
else
2130))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
2131
else
2132)
else
(if i.val < 1459 then
2133
else
2134))
else
(if i.val < 1462 then
(if i.val < 1461 then
2135
else
2136)
else
(if i.val < 1463 then
2137
else
2138)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
2139
else
2140)
else
(if i.val < 1467 then
2141
else
2142))
else
(if i.val < 1470 then
(if i.val < 1469 then
2143
else
655)
else
(if i.val < 1471 then
2144
else
2145))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
2146
else
2147)
else
(if i.val < 1475 then
2148
else
2149))
else
(if i.val < 1478 then
(if i.val < 1477 then
2150
else
2151)
else
(if i.val < 1479 then
2152
else
2153)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
2154
else
2155)
else
(if i.val < 1483 then
2156
else
641))
else
(if i.val < 1486 then
(if i.val < 1485 then
2157
else
2158)
else
(if i.val < 1487 then
2159
else
2160))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
2161
else
2162)
else
(if i.val < 1491 then
1525
else
726))
else
(if i.val < 1494 then
(if i.val < 1493 then
2163
else
757)
else
(if i.val < 1495 then
2164
else
2165)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
2166
else
2167)
else
(if i.val < 1499 then
2168
else
2169))
else
(if i.val < 1502 then
(if i.val < 1501 then
1623
else
2170)
else
(if i.val < 1503 then
2171
else
2172)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
2173
else
2174)
else
(if i.val < 1507 then
782
else
2175))
else
(if i.val < 1510 then
(if i.val < 1509 then
2176
else
2177)
else
(if i.val < 1511 then
2178
else
2179)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
2180
else
2181)
else
(if i.val < 1515 then
2182
else
2183))
else
(if i.val < 1518 then
(if i.val < 1517 then
2184
else
2185)
else
(if i.val < 1519 then
2186
else
2187))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
2188
else
2189)
else
(if i.val < 1523 then
803
else
631))
else
(if i.val < 1526 then
(if i.val < 1525 then
2190
else
1614)
else
(if i.val < 1527 then
2191
else
2192)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
615
else
806)
else
(if i.val < 1531 then
2193
else
898))
else
(if i.val < 1534 then
(if i.val < 1533 then
804
else
805)
else
(if i.val < 1535 then
1392
else
879)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0003 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
880
else
790)
else
(if i.val < 1539 then
1600
else
2194))
else
(if i.val < 1542 then
(if i.val < 1541 then
2195
else
784)
else
(if i.val < 1543 then
760
else
1620)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
2196
else
2197)
else
(if i.val < 1547 then
1549
else
2198))
else
(if i.val < 1550 then
(if i.val < 1549 then
2199
else
2200)
else
(if i.val < 1551 then
1286
else
2201))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
2202
else
2203)
else
(if i.val < 1555 then
1678
else
2204))
else
(if i.val < 1558 then
(if i.val < 1557 then
2205
else
2206)
else
(if i.val < 1559 then
2207
else
2208)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
2209
else
2210)
else
(if i.val < 1563 then
2211
else
2212))
else
(if i.val < 1566 then
(if i.val < 1565 then
2213
else
2214)
else
(if i.val < 1567 then
2215
else
662)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
674
else
2216)
else
(if i.val < 1571 then
2217
else
1646))
else
(if i.val < 1574 then
(if i.val < 1573 then
2218
else
2219)
else
(if i.val < 1575 then
2220
else
2221)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
2222
else
1640)
else
(if i.val < 1579 then
2223
else
2224))
else
(if i.val < 1582 then
(if i.val < 1581 then
2225
else
2226)
else
(if i.val < 1583 then
2227
else
1573))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
1742
else
2228)
else
(if i.val < 1587 then
1316
else
2229))
else
(if i.val < 1590 then
(if i.val < 1589 then
2230
else
2231)
else
(if i.val < 1591 then
2232
else
672)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
2233
else
895)
else
(if i.val < 1595 then
2234
else
2235))
else
(if i.val < 1598 then
(if i.val < 1597 then
886
else
2236)
else
(if i.val < 1599 then
2237
else
752))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
2238
else
2239)
else
(if i.val < 1603 then
684
else
2240))
else
(if i.val < 1606 then
(if i.val < 1605 then
896
else
1625)
else
(if i.val < 1607 then
1521
else
2241)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
2242
else
2243)
else
(if i.val < 1611 then
2244
else
1368))
else
(if i.val < 1614 then
(if i.val < 1613 then
2245
else
1363)
else
(if i.val < 1615 then
1490
else
845))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
764
else
1764)
else
(if i.val < 1619 then
2246
else
2247))
else
(if i.val < 1622 then
(if i.val < 1621 then
1627
else
2248)
else
(if i.val < 1623 then
2249
else
2250)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
833
else
2251)
else
(if i.val < 1627 then
2252
else
1543))
else
(if i.val < 1630 then
(if i.val < 1629 then
2253
else
2254)
else
(if i.val < 1631 then
2255
else
1291)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
2256
else
2257)
else
(if i.val < 1635 then
1362
else
2258))
else
(if i.val < 1638 then
(if i.val < 1637 then
2259
else
2260)
else
(if i.val < 1639 then
2261
else
2262)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
2263
else
2264)
else
(if i.val < 1643 then
2265
else
2266))
else
(if i.val < 1646 then
(if i.val < 1645 then
1488
else
2267)
else
(if i.val < 1647 then
2268
else
2269))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
1287
else
2270)
else
(if i.val < 1651 then
2271
else
1482))
else
(if i.val < 1654 then
(if i.val < 1653 then
1381
else
1319)
else
(if i.val < 1655 then
2272
else
2273)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
1723
else
1322)
else
(if i.val < 1659 then
2274
else
2275))
else
(if i.val < 1662 then
(if i.val < 1661 then
1312
else
2276)
else
(if i.val < 1663 then
890
else
1290)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
2277
else
1592)
else
(if i.val < 1667 then
2278
else
2279))
else
(if i.val < 1670 then
(if i.val < 1669 then
2280
else
2281)
else
(if i.val < 1671 then
2282
else
2283)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
1403
else
1371)
else
(if i.val < 1675 then
2284
else
2285))
else
(if i.val < 1678 then
(if i.val < 1677 then
2286
else
2287)
else
(if i.val < 1679 then
2288
else
2289))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
2290
else
850)
else
(if i.val < 1683 then
2291
else
2292))
else
(if i.val < 1686 then
(if i.val < 1685 then
2293
else
2294)
else
(if i.val < 1687 then
2295
else
1323)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
2296
else
2297)
else
(if i.val < 1691 then
2298
else
2299))
else
(if i.val < 1694 then
(if i.val < 1693 then
888
else
1613)
else
(if i.val < 1695 then
2300
else
2301)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
2302
else
2303)
else
(if i.val < 1699 then
2304
else
1369))
else
(if i.val < 1702 then
(if i.val < 1701 then
2305
else
2306)
else
(if i.val < 1703 then
2307
else
2308)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
1325
else
1419)
else
(if i.val < 1707 then
1329
else
1346))
else
(if i.val < 1710 then
(if i.val < 1709 then
2309
else
2310)
else
(if i.val < 1711 then
2311
else
2312))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
2313
else
2314)
else
(if i.val < 1715 then
2315
else
2316))
else
(if i.val < 1718 then
(if i.val < 1717 then
2317
else
2318)
else
(if i.val < 1719 then
2319
else
2320)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
2321
else
2322)
else
(if i.val < 1723 then
2323
else
2324))
else
(if i.val < 1726 then
(if i.val < 1725 then
2325
else
2326)
else
(if i.val < 1727 then
2327
else
2328))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
2329
else
1505)
else
(if i.val < 1731 then
2330
else
2331))
else
(if i.val < 1734 then
(if i.val < 1733 then
2332
else
719)
else
(if i.val < 1735 then
2333
else
1595)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
1387
else
2334)
else
(if i.val < 1739 then
2335
else
1712))
else
(if i.val < 1742 then
(if i.val < 1741 then
2336
else
2337)
else
(if i.val < 1743 then
2338
else
2339))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
2340
else
2341)
else
(if i.val < 1747 then
2342
else
2343))
else
(if i.val < 1750 then
(if i.val < 1749 then
2344
else
2345)
else
(if i.val < 1751 then
2346
else
2347)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
2348
else
2349)
else
(if i.val < 1755 then
2350
else
2351))
else
(if i.val < 1758 then
(if i.val < 1757 then
2352
else
2353)
else
(if i.val < 1759 then
2354
else
2355)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
2356
else
2357)
else
(if i.val < 1763 then
2358
else
2359))
else
(if i.val < 1766 then
(if i.val < 1765 then
2360
else
811)
else
(if i.val < 1767 then
2361
else
2362)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
2363
else
2364)
else
(if i.val < 1771 then
2365
else
2366))
else
(if i.val < 1774 then
(if i.val < 1773 then
2367
else
2368)
else
(if i.val < 1775 then
849
else
2369))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
2370
else
2371)
else
(if i.val < 1779 then
1301
else
1370))
else
(if i.val < 1782 then
(if i.val < 1781 then
2372
else
1326)
else
(if i.val < 1783 then
2373
else
1652)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
2374
else
2375)
else
(if i.val < 1787 then
2376
else
2377))
else
(if i.val < 1790 then
(if i.val < 1789 then
2378
else
2379)
else
(if i.val < 1791 then
2380
else
1562))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
2381
else
1342)
else
(if i.val < 1795 then
1404
else
2382))
else
(if i.val < 1798 then
(if i.val < 1797 then
1372
else
1366)
else
(if i.val < 1799 then
2383
else
2384)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
1341
else
2385)
else
(if i.val < 1803 then
1661
else
596))
else
(if i.val < 1806 then
(if i.val < 1805 then
597
else
598)
else
(if i.val < 1807 then
599
else
600))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
601
else
602)
else
(if i.val < 1811 then
606
else
607))
else
(if i.val < 1814 then
(if i.val < 1813 then
608
else
609)
else
(if i.val < 1815 then
610
else
611)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
612
else
614)
else
(if i.val < 1819 then
617
else
618))
else
(if i.val < 1822 then
(if i.val < 1821 then
619
else
620)
else
(if i.val < 1823 then
621
else
622)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
623
else
624)
else
(if i.val < 1827 then
625
else
626))
else
(if i.val < 1830 then
(if i.val < 1829 then
627
else
628)
else
(if i.val < 1831 then
629
else
633)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
635
else
636)
else
(if i.val < 1835 then
638
else
643))
else
(if i.val < 1838 then
(if i.val < 1837 then
644
else
646)
else
(if i.val < 1839 then
647
else
648))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
649
else
652)
else
(if i.val < 1843 then
653
else
654))
else
(if i.val < 1846 then
(if i.val < 1845 then
656
else
657)
else
(if i.val < 1847 then
658
else
659)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
661
else
663)
else
(if i.val < 1851 then
665
else
666))
else
(if i.val < 1854 then
(if i.val < 1853 then
669
else
670)
else
(if i.val < 1855 then
671
else
676))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
677
else
678)
else
(if i.val < 1859 then
679
else
681))
else
(if i.val < 1862 then
(if i.val < 1861 then
682
else
686)
else
(if i.val < 1863 then
687
else
688)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
689
else
690)
else
(if i.val < 1867 then
691
else
692))
else
(if i.val < 1870 then
(if i.val < 1869 then
693
else
694)
else
(if i.val < 1871 then
695
else
696))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
697
else
698)
else
(if i.val < 1875 then
699
else
700))
else
(if i.val < 1878 then
(if i.val < 1877 then
701
else
705)
else
(if i.val < 1879 then
706
else
707)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
708
else
709)
else
(if i.val < 1883 then
712
else
713))
else
(if i.val < 1886 then
(if i.val < 1885 then
714
else
715)
else
(if i.val < 1887 then
718
else
720)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
721
else
722)
else
(if i.val < 1891 then
723
else
724))
else
(if i.val < 1894 then
(if i.val < 1893 then
725
else
727)
else
(if i.val < 1895 then
729
else
730)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
732
else
737)
else
(if i.val < 1899 then
741
else
742))
else
(if i.val < 1902 then
(if i.val < 1901 then
743
else
744)
else
(if i.val < 1903 then
745
else
746))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
748
else
751)
else
(if i.val < 1907 then
753
else
755))
else
(if i.val < 1910 then
(if i.val < 1909 then
756
else
758)
else
(if i.val < 1911 then
759
else
761)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
763
else
767)
else
(if i.val < 1915 then
768
else
770))
else
(if i.val < 1918 then
(if i.val < 1917 then
774
else
777)
else
(if i.val < 1919 then
778
else
779)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
781
else
785)
else
(if i.val < 1923 then
786
else
791))
else
(if i.val < 1926 then
(if i.val < 1925 then
792
else
794)
else
(if i.val < 1927 then
795
else
796)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
797
else
798)
else
(if i.val < 1931 then
799
else
800))
else
(if i.val < 1934 then
(if i.val < 1933 then
801
else
808)
else
(if i.val < 1935 then
809
else
810))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
812
else
813)
else
(if i.val < 1939 then
814
else
815))
else
(if i.val < 1942 then
(if i.val < 1941 then
816
else
817)
else
(if i.val < 1943 then
818
else
820)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
821
else
822)
else
(if i.val < 1947 then
823
else
825))
else
(if i.val < 1950 then
(if i.val < 1949 then
827
else
828)
else
(if i.val < 1951 then
829
else
830)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
831
else
832)
else
(if i.val < 1955 then
834
else
835))
else
(if i.val < 1958 then
(if i.val < 1957 then
836
else
837)
else
(if i.val < 1959 then
839
else
840)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
841
else
842)
else
(if i.val < 1963 then
844
else
846))
else
(if i.val < 1966 then
(if i.val < 1965 then
847
else
851)
else
(if i.val < 1967 then
852
else
853))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
854
else
856)
else
(if i.val < 1971 then
857
else
858))
else
(if i.val < 1974 then
(if i.val < 1973 then
859
else
860)
else
(if i.val < 1975 then
861
else
862)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
865
else
866)
else
(if i.val < 1979 then
867
else
868))
else
(if i.val < 1982 then
(if i.val < 1981 then
869
else
870)
else
(if i.val < 1983 then
871
else
872))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
873
else
874)
else
(if i.val < 1987 then
875
else
876))
else
(if i.val < 1990 then
(if i.val < 1989 then
877
else
878)
else
(if i.val < 1991 then
881
else
882)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
884
else
885)
else
(if i.val < 1995 then
887
else
891))
else
(if i.val < 1998 then
(if i.val < 1997 then
892
else
893)
else
(if i.val < 1999 then
894
else
897))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
3014
else
3015)
else
(if i.val < 2003 then
3016
else
1394))
else
(if i.val < 2006 then
(if i.val < 2005 then
1550
else
1648)
else
(if i.val < 2007 then
3017
else
3018)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
1663
else
1631)
else
(if i.val < 2011 then
2714
else
2742))
else
(if i.val < 2014 then
(if i.val < 2013 then
3019
else
3020)
else
(if i.val < 2015 then
2711
else
1337)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
3021
else
2926)
else
(if i.val < 2019 then
1778
else
2827))
else
(if i.val < 2022 then
(if i.val < 2021 then
3022
else
3023)
else
(if i.val < 2023 then
3024
else
2940)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
1660
else
3025)
else
(if i.val < 2027 then
1586
else
2391))
else
(if i.val < 2030 then
(if i.val < 2029 then
3026
else
1653)
else
(if i.val < 2031 then
2516
else
2709))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
1657
else
1687)
else
(if i.val < 2035 then
3027
else
1704))
else
(if i.val < 2038 then
(if i.val < 2037 then
1781
else
2477)
else
(if i.val < 2039 then
3028
else
1706)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
2506
else
1361)
else
(if i.val < 2043 then
3029
else
3030))
else
(if i.val < 2046 then
(if i.val < 2045 then
2571
else
3031)
else
(if i.val < 2047 then
3032
else
3033)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0004 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
2710
else
2608)
else
(if i.val < 2051 then
1800
else
1793))
else
(if i.val < 2054 then
(if i.val < 2053 then
3034
else
1707)
else
(if i.val < 2055 then
2488
else
3035)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
2403
else
2610)
else
(if i.val < 2059 then
3036
else
2682))
else
(if i.val < 2062 then
(if i.val < 2061 then
3037
else
1634)
else
(if i.val < 2063 then
2708
else
1611))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
1699
else
1779)
else
(if i.val < 2067 then
1673
else
1796))
else
(if i.val < 2070 then
(if i.val < 2069 then
2408
else
3038)
else
(if i.val < 2071 then
3039
else
2570)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
3040
else
3041)
else
(if i.val < 2075 then
2499
else
3042))
else
(if i.val < 2078 then
(if i.val < 2077 then
2536
else
1736)
else
(if i.val < 2079 then
3043
else
3044)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
3045
else
2635)
else
(if i.val < 2083 then
2625
else
2494))
else
(if i.val < 2086 then
(if i.val < 2085 then
3046
else
3047)
else
(if i.val < 2087 then
3048
else
3049)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
2552
else
3050)
else
(if i.val < 2091 then
3051
else
1672))
else
(if i.val < 2094 then
(if i.val < 2093 then
1794
else
3052)
else
(if i.val < 2095 then
2927
else
3053))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
2943
else
2763)
else
(if i.val < 2099 then
3054
else
2938))
else
(if i.val < 2102 then
(if i.val < 2101 then
2762
else
2417)
else
(if i.val < 2103 then
2426
else
1705)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
3055
else
2425)
else
(if i.val < 2107 then
2423
else
3056))
else
(if i.val < 2110 then
(if i.val < 2109 then
2475
else
3057)
else
(if i.val < 2111 then
2736
else
2554))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
2764
else
2466)
else
(if i.val < 2115 then
2672
else
2702))
else
(if i.val < 2118 then
(if i.val < 2117 then
3058
else
3059)
else
(if i.val < 2119 then
3060
else
3061)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
3062
else
2424)
else
(if i.val < 2123 then
2862
else
3063))
else
(if i.val < 2126 then
(if i.val < 2125 then
2666
else
2761)
else
(if i.val < 2127 then
2743
else
2901))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
3064
else
3065)
else
(if i.val < 2131 then
1421
else
2468))
else
(if i.val < 2134 then
(if i.val < 2133 then
3066
else
2512)
else
(if i.val < 2135 then
3067
else
2445)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
3068
else
2814)
else
(if i.val < 2139 then
2988
else
3069))
else
(if i.val < 2142 then
(if i.val < 2141 then
2724
else
1364)
else
(if i.val < 2143 then
3070
else
3071)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
1365
else
2861)
else
(if i.val < 2147 then
2990
else
3072))
else
(if i.val < 2150 then
(if i.val < 2149 then
3073
else
3074)
else
(if i.val < 2151 then
3075
else
2480)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
2464
else
2511)
else
(if i.val < 2155 then
3076
else
3077))
else
(if i.val < 2158 then
(if i.val < 2157 then
1651
else
2507)
else
(if i.val < 2159 then
2508
else
3078))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
2517
else
1644)
else
(if i.val < 2163 then
3079
else
3080))
else
(if i.val < 2166 then
(if i.val < 2165 then
2505
else
2492)
else
(if i.val < 2167 then
2502
else
2503)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
2500
else
2388)
else
(if i.val < 2171 then
3081
else
3082))
else
(if i.val < 2174 then
(if i.val < 2173 then
3083
else
2674)
else
(if i.val < 2175 then
1729
else
3084)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
2402
else
3085)
else
(if i.val < 2179 then
1313
else
3086))
else
(if i.val < 2182 then
(if i.val < 2181 then
3087
else
3088)
else
(if i.val < 2183 then
3089
else
3090)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
3091
else
3092)
else
(if i.val < 2187 then
3093
else
3094))
else
(if i.val < 2190 then
(if i.val < 2189 then
2392
else
1606)
else
(if i.val < 2191 then
2910
else
3095))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
3096
else
2879)
else
(if i.val < 2195 then
3097
else
2789))
else
(if i.val < 2198 then
(if i.val < 2197 then
3098
else
3099)
else
(if i.val < 2199 then
2504
else
1426)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
1546
else
2936)
else
(if i.val < 2203 then
3100
else
3101))
else
(if i.val < 2206 then
(if i.val < 2205 then
3102
else
3103)
else
(if i.val < 2207 then
3104
else
3105)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
2800
else
2501)
else
(if i.val < 2211 then
3106
else
1791))
else
(if i.val < 2214 then
(if i.val < 2213 then
3107
else
3108)
else
(if i.val < 2215 then
2478
else
3109)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
3110
else
3111)
else
(if i.val < 2219 then
3112
else
1583))
else
(if i.val < 2222 then
(if i.val < 2221 then
2579
else
3113)
else
(if i.val < 2223 then
3114
else
3115))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
3116
else
2727)
else
(if i.val < 2227 then
2706
else
2631))
else
(if i.val < 2230 then
(if i.val < 2229 then
3117
else
2638)
else
(if i.val < 2231 then
3118
else
3119)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
3120
else
1665)
else
(if i.val < 2235 then
3121
else
1735))
else
(if i.val < 2238 then
(if i.val < 2237 then
3122
else
3123)
else
(if i.val < 2239 then
1538
else
3124))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
3125
else
3126)
else
(if i.val < 2243 then
3127
else
3128))
else
(if i.val < 2246 then
(if i.val < 2245 then
3129
else
3130)
else
(if i.val < 2247 then
3131
else
2581)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
2726
else
2398)
else
(if i.val < 2251 then
1500
else
1605))
else
(if i.val < 2254 then
(if i.val < 2253 then
3132
else
2723)
else
(if i.val < 2255 then
2717
else
2712))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
3133
else
3134)
else
(if i.val < 2259 then
3135
else
3136))
else
(if i.val < 2262 then
(if i.val < 2261 then
3137
else
2956)
else
(if i.val < 2263 then
3138
else
1577)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
2533
else
3139)
else
(if i.val < 2267 then
3140
else
3141))
else
(if i.val < 2270 then
(if i.val < 2269 then
1571
else
2715)
else
(if i.val < 2271 then
2716
else
3142)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
3143
else
3144)
else
(if i.val < 2275 then
1410
else
2883))
else
(if i.val < 2278 then
(if i.val < 2277 then
1802
else
3145)
else
(if i.val < 2279 then
2982
else
3146)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
3147
else
3148)
else
(if i.val < 2283 then
2953
else
1451))
else
(if i.val < 2286 then
(if i.val < 2285 then
3149
else
3150)
else
(if i.val < 2287 then
1378
else
1435))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
1554
else
2412)
else
(if i.val < 2291 then
3151
else
3152))
else
(if i.val < 2294 then
(if i.val < 2293 then
2801
else
2802)
else
(if i.val < 2295 then
2967
else
2491)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
3153
else
3154)
else
(if i.val < 2299 then
2819
else
3155))
else
(if i.val < 2302 then
(if i.val < 2301 then
2832
else
3156)
else
(if i.val < 2303 then
2979
else
3157))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
3158
else
2844)
else
(if i.val < 2307 then
2912
else
3159))
else
(if i.val < 2310 then
(if i.val < 2309 then
3160
else
2486)
else
(if i.val < 2311 then
3161
else
3162)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
3163
else
1739)
else
(if i.val < 2315 then
3164
else
2981))
else
(if i.val < 2318 then
(if i.val < 2317 then
3165
else
3166)
else
(if i.val < 2319 then
3167
else
3168))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
1446
else
1409)
else
(if i.val < 2323 then
1417
else
1374))
else
(if i.val < 2326 then
(if i.val < 2325 then
1656
else
1425)
else
(if i.val < 2327 then
1384
else
2870)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
2878
else
1380)
else
(if i.val < 2331 then
3169
else
2446))
else
(if i.val < 2334 then
(if i.val < 2333 then
3170
else
3171)
else
(if i.val < 2335 then
3172
else
3173)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
3174
else
3175)
else
(if i.val < 2339 then
1584
else
2627))
else
(if i.val < 2342 then
(if i.val < 2341 then
2932
else
2421)
else
(if i.val < 2343 then
2869
else
1304)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
2720
else
3176)
else
(if i.val < 2347 then
1314
else
3177))
else
(if i.val < 2350 then
(if i.val < 2349 then
1303
else
3178)
else
(if i.val < 2351 then
3179
else
2418))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
3180
else
2667)
else
(if i.val < 2355 then
3181
else
2826))
else
(if i.val < 2358 then
(if i.val < 2357 then
3182
else
2722)
else
(if i.val < 2359 then
3183
else
3184)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
1617
else
3185)
else
(if i.val < 2363 then
2811
else
2931))
else
(if i.val < 2366 then
(if i.val < 2365 then
2719
else
2721)
else
(if i.val < 2367 then
3186
else
3187))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
3188
else
3189)
else
(if i.val < 2371 then
2933
else
3190))
else
(if i.val < 2374 then
(if i.val < 2373 then
3191
else
1413)
else
(if i.val < 2375 then
2754
else
3192)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
2621
else
3193)
else
(if i.val < 2379 then
2808
else
3194))
else
(if i.val < 2382 then
(if i.val < 2381 then
3195
else
2793)
else
(if i.val < 2383 then
2856
else
3196))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
2521
else
3197)
else
(if i.val < 2387 then
3198
else
3199))
else
(if i.val < 2390 then
(if i.val < 2389 then
1499
else
3200)
else
(if i.val < 2391 then
2604
else
1317)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
1520
else
3201)
else
(if i.val < 2395 then
3202
else
3203))
else
(if i.val < 2398 then
(if i.val < 2397 then
2823
else
3204)
else
(if i.val < 2399 then
1622
else
3205)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
2482
else
3206)
else
(if i.val < 2403 then
1508
else
1349))
else
(if i.val < 2406 then
(if i.val < 2405 then
3207
else
3208)
else
(if i.val < 2407 then
3209
else
3210)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
1373
else
2946)
else
(if i.val < 2411 then
3211
else
2838))
else
(if i.val < 2414 then
(if i.val < 2413 then
1679
else
3212)
else
(if i.val < 2415 then
3213
else
2955))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
3214
else
1416)
else
(if i.val < 2419 then
1755
else
3215))
else
(if i.val < 2422 then
(if i.val < 2421 then
3216
else
1745)
else
(if i.val < 2423 then
3217
else
1423)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
1443
else
1422)
else
(if i.val < 2427 then
1418
else
2748))
else
(if i.val < 2430 then
(if i.val < 2429 then
2690
else
2580)
else
(if i.val < 2431 then
2557
else
3218)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
3219
else
3220)
else
(if i.val < 2435 then
3221
else
3222))
else
(if i.val < 2438 then
(if i.val < 2437 then
3223
else
3224)
else
(if i.val < 2439 then
3225
else
3226)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
3227
else
3228)
else
(if i.val < 2443 then
2788
else
3229))
else
(if i.val < 2446 then
(if i.val < 2445 then
3230
else
1460)
else
(if i.val < 2447 then
1731
else
3231))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
3232
else
3233)
else
(if i.val < 2451 then
3234
else
3235))
else
(if i.val < 2454 then
(if i.val < 2453 then
3236
else
3237)
else
(if i.val < 2455 then
3238
else
3239)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
3240
else
3241)
else
(if i.val < 2459 then
3242
else
2410))
else
(if i.val < 2462 then
(if i.val < 2461 then
3243
else
3244)
else
(if i.val < 2463 then
3245
else
3246)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
1478
else
2602)
else
(if i.val < 2467 then
1433
else
3247))
else
(if i.val < 2470 then
(if i.val < 2469 then
1456
else
3248)
else
(if i.val < 2471 then
2655
else
2895)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
3249
else
3250)
else
(if i.val < 2475 then
3251
else
1427))
else
(if i.val < 2478 then
(if i.val < 2477 then
3252
else
1327)
else
(if i.val < 2479 then
1565
else
2456))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
1477
else
3253)
else
(if i.val < 2483 then
3254
else
2958))
else
(if i.val < 2486 then
(if i.val < 2485 then
3255
else
3256)
else
(if i.val < 2487 then
1708
else
3257)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
1347
else
3258)
else
(if i.val < 2491 then
3259
else
1686))
else
(if i.val < 2494 then
(if i.val < 2493 then
1495
else
3260)
else
(if i.val < 2495 then
1395
else
3261))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
2649
else
2867)
else
(if i.val < 2499 then
3262
else
1383))
else
(if i.val < 2502 then
(if i.val < 2501 then
1498
else
1560)
else
(if i.val < 2503 then
1496
else
1497)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
1547
else
1494)
else
(if i.val < 2507 then
1330
else
1484))
else
(if i.val < 2510 then
(if i.val < 2509 then
1485
else
2872)
else
(if i.val < 2511 then
2447
else
1479))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
1458
else
2653)
else
(if i.val < 2515 then
3263
else
2469))
else
(if i.val < 2518 then
(if i.val < 2517 then
1320
else
1487)
else
(if i.val < 2519 then
3264
else
2809)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
3265
else
1799)
else
(if i.val < 2523 then
3266
else
2683))
else
(if i.val < 2526 then
(if i.val < 2525 then
3267
else
3268)
else
(if i.val < 2527 then
3269
else
3270)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
2954
else
2922)
else
(if i.val < 2531 then
3271
else
3272))
else
(if i.val < 2534 then
(if i.val < 2533 then
3273
else
1641)
else
(if i.val < 2535 then
3274
else
3275)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
1386
else
3276)
else
(if i.val < 2539 then
3277
else
2923))
else
(if i.val < 2542 then
(if i.val < 2541 then
2925
else
3278)
else
(if i.val < 2543 then
3279
else
2393))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
3280
else
2920)
else
(if i.val < 2547 then
3281
else
2520))
else
(if i.val < 2550 then
(if i.val < 2549 then
3282
else
3283)
else
(if i.val < 2551 then
3284
else
3285)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
1400
else
3286)
else
(if i.val < 2555 then
1430
else
3287))
else
(if i.val < 2558 then
(if i.val < 2557 then
2701
else
3288)
else
(if i.val < 2559 then
2546
else
3289)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0005 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
3290
else
3291)
else
(if i.val < 2563 then
3292
else
3293))
else
(if i.val < 2566 then
(if i.val < 2565 then
3294
else
3295)
else
(if i.val < 2567 then
3296
else
2928)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
3297
else
3298)
else
(if i.val < 2571 then
1377
else
1334))
else
(if i.val < 2574 then
(if i.val < 2573 then
3299
else
2854)
else
(if i.val < 2575 then
3300
else
3301))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
2908
else
3302)
else
(if i.val < 2579 then
3303
else
1574))
else
(if i.val < 2582 then
(if i.val < 2581 then
3304
else
1619)
else
(if i.val < 2583 then
3305
else
3306)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
3307
else
3308)
else
(if i.val < 2587 then
2993
else
3309))
else
(if i.val < 2590 then
(if i.val < 2589 then
2950
else
3310)
else
(if i.val < 2591 then
3311
else
3312)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
3313
else
2449)
else
(if i.val < 2595 then
3314
else
3315))
else
(if i.val < 2598 then
(if i.val < 2597 then
2665
else
3316)
else
(if i.val < 2599 then
3317
else
3318)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
2744
else
3319)
else
(if i.val < 2603 then
3320
else
2873))
else
(if i.val < 2606 then
(if i.val < 2605 then
3321
else
3322)
else
(if i.val < 2607 then
3323
else
3324))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
1340
else
2792)
else
(if i.val < 2611 then
1350
else
2980))
else
(if i.val < 2614 then
(if i.val < 2613 then
3325
else
3326)
else
(if i.val < 2615 then
3327
else
3328)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
3329
else
2917)
else
(if i.val < 2619 then
3330
else
3331))
else
(if i.val < 2622 then
(if i.val < 2621 then
3332
else
1786)
else
(if i.val < 2623 then
3333
else
3334))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
3335
else
1393)
else
(if i.val < 2627 then
3336
else
1743))
else
(if i.val < 2630 then
(if i.val < 2629 then
2859
else
3337)
else
(if i.val < 2631 then
3338
else
1582)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
3339
else
3340)
else
(if i.val < 2635 then
2888
else
1391))
else
(if i.val < 2638 then
(if i.val < 2637 then
3341
else
3342)
else
(if i.val < 2639 then
1587
else
3343))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
3344
else
3345)
else
(if i.val < 2643 then
3346
else
3347))
else
(if i.val < 2646 then
(if i.val < 2645 then
3348
else
3349)
else
(if i.val < 2647 then
3350
else
3351)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
3352
else
3353)
else
(if i.val < 2651 then
2829
else
3354))
else
(if i.val < 2654 then
(if i.val < 2653 then
3355
else
3356)
else
(if i.val < 2655 then
2598
else
3357)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
3358
else
3359)
else
(if i.val < 2659 then
3360
else
3361))
else
(if i.val < 2662 then
(if i.val < 2661 then
2386
else
3362)
else
(if i.val < 2663 then
3363
else
3364)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
3365
else
3366)
else
(if i.val < 2667 then
1447
else
1757))
else
(if i.val < 2670 then
(if i.val < 2669 then
3367
else
3368)
else
(if i.val < 2671 then
3369
else
3370))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
1434
else
3371)
else
(if i.val < 2675 then
1504
else
3372))
else
(if i.val < 2678 then
(if i.val < 2677 then
3373
else
3374)
else
(if i.val < 2679 then
3375
else
3376)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
3377
else
3378)
else
(if i.val < 2683 then
1353
else
3379))
else
(if i.val < 2686 then
(if i.val < 2685 then
3380
else
3381)
else
(if i.val < 2687 then
2605
else
3382)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
3383
else
3384)
else
(if i.val < 2691 then
3385
else
2656))
else
(if i.val < 2694 then
(if i.val < 2693 then
3386
else
3387)
else
(if i.val < 2695 then
3388
else
3389)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
3390
else
3391)
else
(if i.val < 2699 then
3392
else
3393))
else
(if i.val < 2702 then
(if i.val < 2701 then
3394
else
3395)
else
(if i.val < 2703 then
1436
else
3396))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
3397
else
3398)
else
(if i.val < 2707 then
1581
else
3399))
else
(if i.val < 2710 then
(if i.val < 2709 then
1367
else
1321)
else
(if i.val < 2711 then
1339
else
1297)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
1630
else
3400)
else
(if i.val < 2715 then
1292
else
1647))
else
(if i.val < 2718 then
(if i.val < 2717 then
1649
else
1629)
else
(if i.val < 2719 then
2531
else
1769)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
1748
else
1770)
else
(if i.val < 2723 then
1761
else
1628))
else
(if i.val < 2726 then
(if i.val < 2725 then
1465
else
3401)
else
(if i.val < 2727 then
1621
else
1580)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
2874
else
3402)
else
(if i.val < 2731 then
3403
else
3404))
else
(if i.val < 2734 then
(if i.val < 2733 then
3405
else
2803)
else
(if i.val < 2735 then
3406
else
2737))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
1429
else
3407)
else
(if i.val < 2739 then
3408
else
2395))
else
(if i.val < 2742 then
(if i.val < 2741 then
3409
else
3410)
else
(if i.val < 2743 then
1293
else
1449)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
3411
else
3412)
else
(if i.val < 2747 then
3413
else
3414))
else
(if i.val < 2750 then
(if i.val < 2749 then
3415
else
3416)
else
(if i.val < 2751 then
3417
else
3418))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
3419
else
3420)
else
(if i.val < 2755 then
1784
else
2692))
else
(if i.val < 2758 then
(if i.val < 2757 then
2644
else
2871)
else
(if i.val < 2759 then
3421
else
3422)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
2976
else
1448)
else
(if i.val < 2763 then
1415
else
1411))
else
(if i.val < 2766 then
(if i.val < 2765 then
1431
else
2569)
else
(if i.val < 2767 then
2639
else
3423))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
3424
else
3425)
else
(if i.val < 2771 then
3426
else
3427))
else
(if i.val < 2774 then
(if i.val < 2773 then
3428
else
3429)
else
(if i.val < 2775 then
3430
else
3431)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
2857
else
3432)
else
(if i.val < 2779 then
3433
else
2962))
else
(if i.val < 2782 then
(if i.val < 2781 then
3434
else
2909)
else
(if i.val < 2783 then
2752
else
3435)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
3436
else
3437)
else
(if i.val < 2787 then
3438
else
2419))
else
(if i.val < 2790 then
(if i.val < 2789 then
3439
else
1540)
else
(if i.val < 2791 then
3440
else
3441)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
3442
else
1792)
else
(if i.val < 2795 then
3443
else
3444))
else
(if i.val < 2798 then
(if i.val < 2797 then
3445
else
2853)
else
(if i.val < 2799 then
3446
else
3447))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
1559
else
1683)
else
(if i.val < 2803 then
1684
else
2804))
else
(if i.val < 2806 then
(if i.val < 2805 then
2733
else
2753)
else
(if i.val < 2807 then
3448
else
3449)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
1788
else
3450)
else
(if i.val < 2811 then
2564
else
1767))
else
(if i.val < 2814 then
(if i.val < 2813 then
3451
else
3452)
else
(if i.val < 2815 then
1462
else
3012))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
3453
else
2750)
else
(if i.val < 2819 then
3454
else
1690))
else
(if i.val < 2822 then
(if i.val < 2821 then
3455
else
2440)
else
(if i.val < 2823 then
3456
else
3457)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
3458
else
2768)
else
(if i.val < 2827 then
1759
else
1302))
else
(if i.val < 2830 then
(if i.val < 2829 then
3459
else
3460)
else
(if i.val < 2831 then
2855
else
2387))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
1694
else
2659)
else
(if i.val < 2835 then
3461
else
3462))
else
(if i.val < 2838 then
(if i.val < 2837 then
2769
else
3463)
else
(if i.val < 2839 then
3464
else
2399)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
3465
else
3466)
else
(if i.val < 2843 then
3467
else
3468))
else
(if i.val < 2846 then
(if i.val < 2845 then
1700
else
2559)
else
(if i.val < 2847 then
3469
else
2586)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
2537
else
2626)
else
(if i.val < 2851 then
3470
else
2921))
else
(if i.val < 2854 then
(if i.val < 2853 then
3471
else
3472)
else
(if i.val < 2855 then
3473
else
3474)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
1795
else
3475)
else
(if i.val < 2859 then
2957
else
3476))
else
(if i.val < 2862 then
(if i.val < 2861 then
2401
else
1471)
else
(if i.val < 2863 then
1444
else
2777))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
3477
else
3005)
else
(if i.val < 2867 then
2991
else
3478))
else
(if i.val < 2870 then
(if i.val < 2869 then
2487
else
1746)
else
(if i.val < 2871 then
1726
else
3479)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
3480
else
3481)
else
(if i.val < 2875 then
3482
else
3483))
else
(if i.val < 2878 then
(if i.val < 2877 then
3484
else
3485)
else
(if i.val < 2879 then
1727
else
1530))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
3486
else
3487)
else
(if i.val < 2883 then
3488
else
1659))
else
(if i.val < 2886 then
(if i.val < 2885 then
2524
else
3489)
else
(if i.val < 2887 then
3490
else
2438)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
3491
else
2441)
else
(if i.val < 2891 then
3492
else
3493))
else
(if i.val < 2894 then
(if i.val < 2893 then
2812
else
3494)
else
(if i.val < 2895 then
2770
else
3495))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
3496
else
3497)
else
(if i.val < 2899 then
3498
else
3499))
else
(if i.val < 2902 then
(if i.val < 2901 then
3500
else
1450)
else
(if i.val < 2903 then
2413
else
2457)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
2448
else
3501)
else
(if i.val < 2907 then
3502
else
3503))
else
(if i.val < 2910 then
(if i.val < 2909 then
3504
else
3505)
else
(if i.val < 2911 then
1524
else
3506)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
1701
else
2422)
else
(if i.val < 2915 then
3507
else
3508))
else
(if i.val < 2918 then
(if i.val < 2917 then
3509
else
3510)
else
(if i.val < 2919 then
3511
else
3512)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
3513
else
3514)
else
(if i.val < 2923 then
3515
else
3516))
else
(if i.val < 2926 then
(if i.val < 2925 then
3517
else
3518)
else
(if i.val < 2927 then
1300
else
1406))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
3519
else
2729)
else
(if i.val < 2931 then
2984
else
1768))
else
(if i.val < 2934 then
(if i.val < 2933 then
1744
else
1776)
else
(if i.val < 2935 then
3520
else
2820)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
1551
else
2681)
else
(if i.val < 2939 then
1414
else
2741))
else
(if i.val < 2942 then
(if i.val < 2941 then
1310
else
2544)
else
(if i.val < 2943 then
3521
else
1408)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
2985
else
3522)
else
(if i.val < 2947 then
3523
else
3524))
else
(if i.val < 2950 then
(if i.val < 2949 then
3525
else
3004)
else
(if i.val < 2951 then
3526
else
3527)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
3528
else
1670)
else
(if i.val < 2955 then
3529
else
3530))
else
(if i.val < 2958 then
(if i.val < 2957 then
1638
else
2972)
else
(if i.val < 2959 then
3531
else
3532))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
3533
else
3534)
else
(if i.val < 2963 then
3535
else
3536))
else
(if i.val < 2966 then
(if i.val < 2965 then
2738
else
3537)
else
(if i.val < 2967 then
3538
else
1685)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
3539
else
3540)
else
(if i.val < 2971 then
3008
else
3541))
else
(if i.val < 2974 then
(if i.val < 2973 then
2858
else
3542)
else
(if i.val < 2975 then
3543
else
3544)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
3545
else
3546)
else
(if i.val < 2979 then
3547
else
1696))
else
(if i.val < 2982 then
(if i.val < 2981 then
3548
else
1714)
else
(if i.val < 2983 then
1666
else
2758)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
3549
else
3550)
else
(if i.val < 2987 then
3551
else
3552))
else
(if i.val < 2990 then
(if i.val < 2989 then
1463
else
3553)
else
(if i.val < 2991 then
1472
else
3554))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
2450
else
2847)
else
(if i.val < 2995 then
3555
else
3556))
else
(if i.val < 2998 then
(if i.val < 2997 then
2942
else
3003)
else
(if i.val < 2999 then
3557
else
3558)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
2968
else
3559)
else
(if i.val < 3003 then
2918
else
3560))
else
(if i.val < 3006 then
(if i.val < 3005 then
3561
else
3562)
else
(if i.val < 3007 then
3563
else
2526))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
3564
else
3565)
else
(if i.val < 3011 then
3566
else
3567))
else
(if i.val < 3014 then
(if i.val < 3013 then
3568
else
2485)
else
(if i.val < 3015 then
1282
else
1283)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
1284
else
1288)
else
(if i.val < 3019 then
1289
else
1294))
else
(if i.val < 3022 then
(if i.val < 3021 then
1295
else
1299)
else
(if i.val < 3023 then
1305
else
1306))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
1308
else
1315)
else
(if i.val < 3027 then
1318
else
1324))
else
(if i.val < 3030 then
(if i.val < 3029 then
1328
else
1332)
else
(if i.val < 3031 then
1333
else
1335)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
1336
else
1338)
else
(if i.val < 3035 then
1345
else
1348))
else
(if i.val < 3038 then
(if i.val < 3037 then
1351
else
1354)
else
(if i.val < 3039 then
1375
else
1376)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
1379
else
1382)
else
(if i.val < 3043 then
1385
else
1388))
else
(if i.val < 3046 then
(if i.val < 3045 then
1389
else
1390)
else
(if i.val < 3047 then
1396
else
1397)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
1398
else
1399)
else
(if i.val < 3051 then
1401
else
1402))
else
(if i.val < 3054 then
(if i.val < 3053 then
1405
else
1407)
else
(if i.val < 3055 then
1412
else
1420))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
1424
else
1428)
else
(if i.val < 3059 then
1437
else
1439))
else
(if i.val < 3062 then
(if i.val < 3061 then
1440
else
1441)
else
(if i.val < 3063 then
1442
else
1445)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
1452
else
1453)
else
(if i.val < 3067 then
1457
else
1459))
else
(if i.val < 3070 then
(if i.val < 3069 then
1461
else
1464)
else
(if i.val < 3071 then
1467
else
1468)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0006 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 3328 then
(if i.val < 3200 then
(if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
1473
else
1474)
else
(if i.val < 3075 then
1475
else
1476))
else
(if i.val < 3078 then
(if i.val < 3077 then
1480
else
1481)
else
(if i.val < 3079 then
1486
else
1489)))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
1492
else
1501)
else
(if i.val < 3083 then
1502
else
1503))
else
(if i.val < 3086 then
(if i.val < 3085 then
1507
else
1509)
else
(if i.val < 3087 then
1511
else
1512))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
1513
else
1514)
else
(if i.val < 3091 then
1515
else
1516))
else
(if i.val < 3094 then
(if i.val < 3093 then
1517
else
1518)
else
(if i.val < 3095 then
1519
else
1526)))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
1527
else
1539)
else
(if i.val < 3099 then
1544
else
1545))
else
(if i.val < 3102 then
(if i.val < 3101 then
1552
else
1553)
else
(if i.val < 3103 then
1555
else
1556)))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
1557
else
1558)
else
(if i.val < 3107 then
1561
else
1563))
else
(if i.val < 3110 then
(if i.val < 3109 then
1564
else
1566)
else
(if i.val < 3111 then
1569
else
1570)))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
1572
else
1575)
else
(if i.val < 3115 then
1576
else
1578))
else
(if i.val < 3118 then
(if i.val < 3117 then
1579
else
1585)
else
(if i.val < 3119 then
1588
else
1589))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
1590
else
1594)
else
(if i.val < 3123 then
1597
else
1598))
else
(if i.val < 3126 then
(if i.val < 3125 then
1601
else
1603)
else
(if i.val < 3127 then
1607
else
1608)))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
1609
else
1610)
else
(if i.val < 3131 then
1612
else
1618))
else
(if i.val < 3134 then
(if i.val < 3133 then
1626
else
1632)
else
(if i.val < 3135 then
1633
else
1635))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
1636
else
1637)
else
(if i.val < 3139 then
1639
else
1642))
else
(if i.val < 3142 then
(if i.val < 3141 then
1643
else
1645)
else
(if i.val < 3143 then
1650
else
1654)))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
1655
else
1664)
else
(if i.val < 3147 then
1667
else
1668))
else
(if i.val < 3150 then
(if i.val < 3149 then
1669
else
1674)
else
(if i.val < 3151 then
1675
else
1680))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
1682
else
1688)
else
(if i.val < 3155 then
1689
else
1691))
else
(if i.val < 3158 then
(if i.val < 3157 then
1695
else
1697)
else
(if i.val < 3159 then
1698
else
1702)))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
1703
else
1709)
else
(if i.val < 3163 then
1710
else
1711))
else
(if i.val < 3166 then
(if i.val < 3165 then
1713
else
1715)
else
(if i.val < 3167 then
1716
else
1717)))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
1718
else
1730)
else
(if i.val < 3171 then
1732
else
1734))
else
(if i.val < 3174 then
(if i.val < 3173 then
1737
else
1738)
else
(if i.val < 3175 then
1740
else
1741)))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
1749
else
1751)
else
(if i.val < 3179 then
1753
else
1754))
else
(if i.val < 3182 then
(if i.val < 3181 then
1756
else
1758)
else
(if i.val < 3183 then
1760
else
1762))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
1763
else
1766)
else
(if i.val < 3187 then
1771
else
1772))
else
(if i.val < 3190 then
(if i.val < 3189 then
1773
else
1775)
else
(if i.val < 3191 then
1777
else
1780)))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
1785
else
1787)
else
(if i.val < 3195 then
1789
else
1790))
else
(if i.val < 3198 then
(if i.val < 3197 then
1798
else
1801)
else
(if i.val < 3199 then
2660
else
2831)))))))
else
(if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
3988
else
2543)
else
(if i.val < 3203 then
3898
else
2739))
else
(if i.val < 3206 then
(if i.val < 3205 then
3660
else
2839)
else
(if i.val < 3207 then
2860
else
3931)))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
3663
else
3932)
else
(if i.val < 3211 then
3989
else
2459))
else
(if i.val < 3214 then
(if i.val < 3213 then
2902
else
3812)
else
(if i.val < 3215 then
3717
else
2787))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
3570
else
2913)
else
(if i.val < 3219 then
3990
else
3574))
else
(if i.val < 3222 then
(if i.val < 3221 then
3850
else
3606)
else
(if i.val < 3223 then
3575
else
3978)))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
3813
else
2887)
else
(if i.val < 3227 then
3662
else
2821))
else
(if i.val < 3230 then
(if i.val < 3229 then
2889
else
3664)
else
(if i.val < 3231 then
3806
else
2510)))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
2904
else
2593)
else
(if i.val < 3235 then
2992
else
3635))
else
(if i.val < 3238 then
(if i.val < 3237 then
3991
else
3992)
else
(if i.val < 3239 then
3933
else
3634)))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
2479
else
2903)
else
(if i.val < 3243 then
3993
else
3657))
else
(if i.val < 3246 then
(if i.val < 3245 then
3817
else
3994)
else
(if i.val < 3247 then
3626
else
3849))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
2515
else
3995)
else
(if i.val < 3251 then
3996
else
3946))
else
(if i.val < 3254 then
(if i.val < 3253 then
3902
else
3997)
else
(if i.val < 3255 then
2400
else
3998)))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
3013
else
2868)
else
(if i.val < 3259 then
3641
else
3751))
else
(if i.val < 3262 then
(if i.val < 3261 then
3999
else
4000)
else
(if i.val < 3263 then
3672
else
4001))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
3810
else
2547)
else
(if i.val < 3267 then
4002
else
2884))
else
(if i.val < 3270 then
(if i.val < 3269 then
3614
else
3007)
else
(if i.val < 3271 then
4003
else
3654)))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
2718
else
4004)
else
(if i.val < 3275 then
3720
else
3704))
else
(if i.val < 3278 then
(if i.val < 3277 then
2848
else
3630)
else
(if i.val < 3279 then
3943
else
3677))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
2941
else
2558)
else
(if i.val < 3283 then
3695
else
3709))
else
(if i.val < 3286 then
(if i.val < 3285 then
3757
else
3691)
else
(if i.val < 3287 then
3636
else
3909)))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
2430
else
2845)
else
(if i.val < 3291 then
4005
else
4006))
else
(if i.val < 3294 then
(if i.val < 3293 then
3785
else
3653)
else
(if i.val < 3295 then
2810
else
3756)))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
3671
else
3842)
else
(if i.val < 3299 then
2765
else
3591))
else
(if i.val < 3302 then
(if i.val < 3301 then
4007
else
3588)
else
(if i.val < 3303 then
3949
else
4008)))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
2429
else
3841)
else
(if i.val < 3307 then
3839
else
3762))
else
(if i.val < 3310 then
(if i.val < 3309 then
3594
else
3602)
else
(if i.val < 3311 then
4009
else
3659))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
3843
else
3844)
else
(if i.val < 3315 then
3629
else
3775))
else
(if i.val < 3318 then
(if i.val < 3317 then
4010
else
2654)
else
(if i.val < 3319 then
3838
else
3877)))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
2465
else
2390)
else
(if i.val < 3323 then
2686
else
3714))
else
(if i.val < 3326 then
(if i.val < 3325 then
4011
else
3837)
else
(if i.val < 3327 then
3871
else
4012))))))))
else
(if i.val < 3456 then
(if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
3638
else
3930)
else
(if i.val < 3331 then
3601
else
3867))
else
(if i.val < 3334 then
(if i.val < 3333 then
3798
else
3803)
else
(if i.val < 3335 then
3979
else
3593)))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
2849
else
3661)
else
(if i.val < 3339 then
3651
else
3619))
else
(if i.val < 3342 then
(if i.val < 3341 then
4013
else
3875)
else
(if i.val < 3343 then
3592
else
2766))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
3818
else
3678)
else
(if i.val < 3347 then
4014
else
4015))
else
(if i.val < 3350 then
(if i.val < 3349 then
2756
else
4016)
else
(if i.val < 3351 then
4017
else
4018)))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
3582
else
2496)
else
(if i.val < 3355 then
4019
else
4020))
else
(if i.val < 3358 then
(if i.val < 3357 then
2513
else
2470)
else
(if i.val < 3359 then
2691
else
3650)))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
3658
else
2833)
else
(if i.val < 3363 then
4021
else
4022))
else
(if i.val < 3366 then
(if i.val < 3365 then
3700
else
4023)
else
(if i.val < 3367 then
2596
else
4024)))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
3571
else
3573)
else
(if i.val < 3371 then
3922
else
3782))
else
(if i.val < 3374 then
(if i.val < 3373 then
3947
else
4025)
else
(if i.val < 3375 then
4026
else
4027))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
3769
else
4028)
else
(if i.val < 3379 then
2937
else
2523))
else
(if i.val < 3382 then
(if i.val < 3381 then
3944
else
3815)
else
(if i.val < 3383 then
3889
else
4029)))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
4030
else
2428)
else
(if i.val < 3387 then
2755
else
3890))
else
(if i.val < 3390 then
(if i.val < 3389 then
4031
else
3584)
else
(if i.val < 3391 then
3896
else
3938))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
4032
else
4033)
else
(if i.val < 3395 then
3576
else
2556))
else
(if i.val < 3398 then
(if i.val < 3397 then
3598
else
3740)
else
(if i.val < 3399 then
3913
else
3848)))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
4034
else
3655)
else
(if i.val < 3403 then
2929
else
4035))
else
(if i.val < 3406 then
(if i.val < 3405 then
3656
else
3819)
else
(if i.val < 3407 then
3926
else
2735))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
2964
else
3585)
else
(if i.val < 3411 then
2939
else
2600))
else
(if i.val < 3414 then
(if i.val < 3413 then
3976
else
3745)
else
(if i.val < 3415 then
4036
else
2427)))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
3763
else
2817)
else
(if i.val < 3419 then
3870
else
2782))
else
(if i.val < 3422 then
(if i.val < 3421 then
2805
else
2983)
else
(if i.val < 3423 then
3862
else
3869)))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
2825
else
2836)
else
(if i.val < 3427 then
2894
else
4037))
else
(if i.val < 3430 then
(if i.val < 3429 then
4038
else
3761)
else
(if i.val < 3431 then
4039
else
3840)))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
2863
else
3820)
else
(if i.val < 3435 then
4040
else
4041))
else
(if i.val < 3438 then
(if i.val < 3437 then
4042
else
4043)
else
(if i.val < 3439 then
3855
else
2442))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
4044
else
3856)
else
(if i.val < 3443 then
2609
else
4045))
else
(if i.val < 3446 then
(if i.val < 3445 then
3888
else
4046)
else
(if i.val < 3447 then
4047
else
3615)))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
4048
else
3983)
else
(if i.val < 3451 then
2519
else
2892))
else
(if i.val < 3454 then
(if i.val < 3453 then
4049
else
3940)
else
(if i.val < 3455 then
3789
else
2935)))))))
else
(if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
4050
else
2396)
else
(if i.val < 3459 then
3814
else
3595))
else
(if i.val < 3462 then
(if i.val < 3461 then
2650
else
4051)
else
(if i.val < 3463 then
3912
else
4052)))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
2411
else
3881)
else
(if i.val < 3467 then
3917
else
3692))
else
(if i.val < 3470 then
(if i.val < 3469 then
3742
else
4053)
else
(if i.val < 3471 then
4054
else
3577))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
2797
else
2573)
else
(if i.val < 3475 then
2830
else
2776))
else
(if i.val < 3478 then
(if i.val < 3477 then
2628
else
4055)
else
(if i.val < 3479 then
2497
else
2757)))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
2509
else
2603)
else
(if i.val < 3483 then
2728
else
3739))
else
(if i.val < 3486 then
(if i.val < 3485 then
4056
else
3777)
else
(if i.val < 3487 then
3628
else
3962)))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
3665
else
4057)
else
(if i.val < 3491 then
4058
else
2634))
else
(if i.val < 3494 then
(if i.val < 3493 then
3866
else
4059)
else
(if i.val < 3495 then
3878
else
2471)))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
3847
else
3647)
else
(if i.val < 3499 then
4060
else
3914))
else
(if i.val < 3502 then
(if i.val < 3501 then
3770
else
3816)
else
(if i.val < 3503 then
4061
else
3821))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
2576
else
2781)
else
(if i.val < 3507 then
4062
else
4063))
else
(if i.val < 3510 then
(if i.val < 3509 then
4064
else
3706)
else
(if i.val < 3511 then
2617
else
3002)))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
3836
else
2545)
else
(if i.val < 3515 then
2851
else
2529))
else
(if i.val < 3518 then
(if i.val < 3517 then
2539
else
3643)
else
(if i.val < 3519 then
2540
else
2567))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
3620
else
2996)
else
(if i.val < 3523 then
4065
else
2409))
else
(if i.val < 3526 then
(if i.val < 3525 then
4066
else
3854)
else
(if i.val < 3527 then
2588
else
4067)))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
3639
else
2528)
else
(if i.val < 3531 then
2415
else
2483))
else
(if i.val < 3534 then
(if i.val < 3533 then
4068
else
3604)
else
(if i.val < 3535 then
3694
else
2779))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
3835
else
4069)
else
(if i.val < 3539 then
3808
else
3000))
else
(if i.val < 3542 then
(if i.val < 3541 then
3637
else
4070)
else
(if i.val < 3543 then
3884
else
3879)))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
3746
else
2760)
else
(if i.val < 3547 then
4071
else
4072))
else
(if i.val < 3550 then
(if i.val < 3549 then
2611
else
2930)
else
(if i.val < 3551 then
2944
else
4073)))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
3581
else
3747)
else
(if i.val < 3555 then
2866
else
3864))
else
(if i.val < 3558 then
(if i.val < 3557 then
3743
else
4074)
else
(if i.val < 3559 then
3583
else
3646)))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
2997
else
2949)
else
(if i.val < 3563 then
2865
else
3906))
else
(if i.val < 3566 then
(if i.val < 3565 then
2970
else
3586)
else
(if i.val < 3567 then
4075
else
3667))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
2815
else
4076)
else
(if i.val < 3571 then
2420
else
2669))
else
(if i.val < 3574 then
(if i.val < 3573 then
3741
else
2670)
else
(if i.val < 3575 then
2432
else
2435)))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
2700
else
2852)
else
(if i.val < 3579 then
4077
else
4078))
else
(if i.val < 3582 then
(if i.val < 3581 then
3569
else
2987)
else
(if i.val < 3583 then
2648
else
2999)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0007 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 3840 then
(if i.val < 3712 then
(if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
2695
else
2740)
else
(if i.val < 3587 then
3009
else
4079))
else
(if i.val < 3590 then
(if i.val < 3589 then
2575
else
4080)
else
(if i.val < 3591 then
4081
else
2572)))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
2637
else
2624)
else
(if i.val < 3595 then
2585
else
2828))
else
(if i.val < 3598 then
(if i.val < 3597 then
3784
else
3950)
else
(if i.val < 3599 then
2703
else
4082))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
3788
else
2618)
else
(if i.val < 3603 then
2587
else
4083))
else
(if i.val < 3606 then
(if i.val < 3605 then
2960
else
3596)
else
(if i.val < 3607 then
2434
else
3718)))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
4084
else
3684)
else
(if i.val < 3611 then
4085
else
3685))
else
(if i.val < 3614 then
(if i.val < 3613 then
3618
else
3984)
else
(if i.val < 3615 then
2525
else
2799)))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
3980
else
3791)
else
(if i.val < 3619 then
4086
else
2632))
else
(if i.val < 3622 then
(if i.val < 3621 then
2934
else
4087)
else
(if i.val < 3623 then
4088
else
4089)))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
3642
else
4090)
else
(if i.val < 3627 then
2463
else
3911))
else
(if i.val < 3630 then
(if i.val < 3629 then
2880
else
2594)
else
(if i.val < 3631 then
2538
else
3967))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
4091
else
3939)
else
(if i.val < 3635 then
2455
else
2451))
else
(if i.val < 3638 then
(if i.val < 3637 then
2553
else
2969)
else
(if i.val < 3639 then
2615
else
2952)))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
4092
else
2489)
else
(if i.val < 3643 then
3729
else
2924))
else
(if i.val < 3646 then
(if i.val < 3645 then
3958
else
4093)
else
(if i.val < 3647 then
3001
else
2897))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
4094
else
4095)
else
(if i.val < 3651 then
2657
else
2630))
else
(if i.val < 3654 then
(if i.val < 3653 then
3823
else
2563)
else
(if i.val < 3655 then
2530
else
2725)))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
2731
else
2460)
else
(if i.val < 3659 then
2658
else
2590))
else
(if i.val < 3662 then
(if i.val < 3661 then
2397
else
2629)
else
(if i.val < 3663 then
2439
else
2405))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
2443
else
2882)
else
(if i.val < 3667 then
4096
else
3011))
else
(if i.val < 3670 then
(if i.val < 3669 then
3985
else
4097)
else
(if i.val < 3671 then
4098
else
2566)))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
2498
else
4099)
else
(if i.val < 3675 then
4100
else
4101))
else
(if i.val < 3678 then
(if i.val < 3677 then
3957
else
2542)
else
(if i.val < 3679 then
2641
else
4102)))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
4103
else
4104)
else
(if i.val < 3683 then
4105
else
4106))
else
(if i.val < 3686 then
(if i.val < 3685 then
4107
else
3730)
else
(if i.val < 3687 then
3941
else
4108)))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
3907
else
3764)
else
(if i.val < 3691 then
3710
else
2551))
else
(if i.val < 3694 then
(if i.val < 3693 then
2842
else
3744)
else
(if i.val < 3695 then
2961
else
2548))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
3891
else
3696)
else
(if i.val < 3699 then
4109
else
3883))
else
(if i.val < 3702 then
(if i.val < 3701 then
2663
else
3673)
else
(if i.val < 3703 then
3753
else
4110)))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
2535
else
3822)
else
(if i.val < 3707 then
2916
else
4111))
else
(if i.val < 3710 then
(if i.val < 3709 then
4112
else
2549)
else
(if i.val < 3711 then
3801
else
3768)))))))
else
(if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
3792
else
4113)
else
(if i.val < 3715 then
2606
else
4114))
else
(if i.val < 3718 then
(if i.val < 3717 then
4115
else
2416)
else
(if i.val < 3719 then
4116
else
4117)))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
2534
else
4118)
else
(if i.val < 3723 then
4119
else
3621))
else
(if i.val < 3726 then
(if i.val < 3725 then
4120
else
3904)
else
(if i.val < 3727 then
4121
else
4122))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
3699
else
3624)
else
(if i.val < 3731 then
3611
else
4123))
else
(if i.val < 3734 then
(if i.val < 3733 then
3830
else
4124)
else
(if i.val < 3735 then
4125
else
4126)))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
4127
else
4128)
else
(if i.val < 3739 then
4129
else
2875))
else
(if i.val < 3742 then
(if i.val < 3741 then
2704
else
4130)
else
(if i.val < 3743 then
2843
else
2995)))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
4131
else
2746)
else
(if i.val < 3747 then
2975
else
2989))
else
(if i.val < 3750 then
(if i.val < 3749 then
3771
else
4132)
else
(if i.val < 3751 then
3759
else
2490)))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
4133
else
4134)
else
(if i.val < 3755 then
3832
else
3749))
else
(if i.val < 3758 then
(if i.val < 3757 then
2565
else
2550)
else
(if i.val < 3759 then
3908
else
4135))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
4136
else
2773)
else
(if i.val < 3763 then
2584
else
2749))
else
(if i.val < 3766 then
(if i.val < 3765 then
3965
else
4137)
else
(if i.val < 3767 then
4138
else
3971)))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
4139
else
2679)
else
(if i.val < 3771 then
2900
else
4140))
else
(if i.val < 3774 then
(if i.val < 3773 then
3942
else
4141)
else
(if i.val < 3775 then
3794
else
2595))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
4142
else
2877)
else
(if i.val < 3779 then
4143
else
4144))
else
(if i.val < 3782 then
(if i.val < 3781 then
4145
else
4146)
else
(if i.val < 3783 then
2673
else
4147)))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
3605
else
2562)
else
(if i.val < 3787 then
4148
else
4149))
else
(if i.val < 3790 then
(if i.val < 3789 then
3809
else
2818)
else
(if i.val < 3791 then
4150
else
4151))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
4152
else
4153)
else
(if i.val < 3795 then
4154
else
3861))
else
(if i.val < 3798 then
(if i.val < 3797 then
3982
else
3674)
else
(if i.val < 3799 then
2620
else
3880)))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
3579
else
3690)
else
(if i.val < 3803 then
3826
else
2622))
else
(if i.val < 3806 then
(if i.val < 3805 then
4155
else
3783)
else
(if i.val < 3807 then
2444
else
3960)))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
2966
else
3600)
else
(if i.val < 3811 then
2518
else
3831))
else
(if i.val < 3814 then
(if i.val < 3813 then
2414
else
2437)
else
(if i.val < 3815 then
2824
else
2685)))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
2905
else
2461)
else
(if i.val < 3819 then
2640
else
2732))
else
(if i.val < 3822 then
(if i.val < 3821 then
2778
else
2907)
else
(if i.val < 3823 then
4156
else
3915))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
4157
else
3851)
else
(if i.val < 3827 then
4158
else
3799))
else
(if i.val < 3830 then
(if i.val < 3829 then
4159
else
3811)
else
(if i.val < 3831 then
4160
else
3829)))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
3969
else
4161)
else
(if i.val < 3835 then
3825
else
2963))
else
(if i.val < 3838 then
(if i.val < 3837 then
2919
else
2612)
else
(if i.val < 3839 then
2599
else
2583))))))))
else
(if i.val < 3968 then
(if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
2775
else
2582)
else
(if i.val < 3843 then
2568
else
2591))
else
(if i.val < 3846 then
(if i.val < 3845 then
2592
else
3721)
else
(if i.val < 3847 then
3780
else
2896)))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
2707
else
2467)
else
(if i.val < 3851 then
2433
else
3834))
else
(if i.val < 3854 then
(if i.val < 3853 then
4162
else
3959)
else
(if i.val < 3855 then
2948
else
2786))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
2791
else
4163)
else
(if i.val < 3859 then
3868
else
3853))
else
(if i.val < 3862 then
(if i.val < 3861 then
3622
else
4164)
else
(if i.val < 3863 then
2759
else
4165)))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
2994
else
3752)
else
(if i.val < 3867 then
2890
else
2619))
else
(if i.val < 3870 then
(if i.val < 3869 then
4166
else
2767)
else
(if i.val < 3871 then
2751
else
2613)))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
4167
else
3765)
else
(if i.val < 3875 then
3796
else
2636))
else
(if i.val < 3878 then
(if i.val < 3877 then
3760
else
2601)
else
(if i.val < 3879 then
2893
else
2974)))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
3827
else
2840)
else
(if i.val < 3883 then
4168
else
3728))
else
(if i.val < 3886 then
(if i.val < 3885 then
2973
else
3905)
else
(if i.val < 3887 then
3734
else
3731))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
2795
else
2687)
else
(if i.val < 3891 then
2693
else
3697))
else
(if i.val < 3894 then
(if i.val < 3893 then
4169
else
4170)
else
(if i.val < 3895 then
3778
else
3955)))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
2696
else
4171)
else
(if i.val < 3899 then
2394
else
3610))
else
(if i.val < 3902 then
(if i.val < 3901 then
3708
else
4172)
else
(if i.val < 3903 then
2476
else
3824))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
4173
else
4174)
else
(if i.val < 3907 then
3006
else
4175))
else
(if i.val < 3910 then
(if i.val < 3909 then
3981
else
2555)
else
(if i.val < 3911 then
3852
else
4176)))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
2835
else
2705)
else
(if i.val < 3915 then
2899
else
3652))
else
(if i.val < 3918 then
(if i.val < 3917 then
4177
else
2841)
else
(if i.val < 3919 then
3963
else
3928))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
4178
else
4179)
else
(if i.val < 3923 then
2671
else
4180))
else
(if i.val < 3926 then
(if i.val < 3925 then
4181
else
3616)
else
(if i.val < 3927 then
2734
else
3719)))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
4182
else
4183)
else
(if i.val < 3931 then
2616
else
2404))
else
(if i.val < 3934 then
(if i.val < 3933 then
2406
else
2454)
else
(if i.val < 3935 then
3736
else
3737)))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
4184
else
4185)
else
(if i.val < 3939 then
2697
else
3975))
else
(if i.val < 3942 then
(if i.val < 3941 then
2816
else
4186)
else
(if i.val < 3943 then
4187
else
2541)))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
2684
else
4188)
else
(if i.val < 3947 then
2474
else
2675))
else
(if i.val < 3950 then
(if i.val < 3949 then
3679
else
2577)
else
(if i.val < 3951 then
4189
else
4190))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
3683
else
4191)
else
(if i.val < 3955 then
4192
else
4193))
else
(if i.val < 3958 then
(if i.val < 3957 then
3953
else
4194)
else
(if i.val < 3959 then
4195
else
3859)))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
4196
else
3804)
else
(if i.val < 3963 then
2881
else
4197))
else
(if i.val < 3966 then
(if i.val < 3965 then
3916
else
3689)
else
(if i.val < 3967 then
3924
else
4198)))))))
else
(if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
4199
else
3754)
else
(if i.val < 3971 then
3738
else
4200))
else
(if i.val < 3974 then
(if i.val < 3973 then
4201
else
3645)
else
(if i.val < 3975 then
4202
else
3633)))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
2745
else
3670)
else
(if i.val < 3979 then
2436
else
2623))
else
(if i.val < 3982 then
(if i.val < 3981 then
3925
else
3758)
else
(if i.val < 3983 then
3874
else
2807))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
4203
else
4204)
else
(if i.val < 3987 then
4205
else
3954))
else
(if i.val < 3990 then
(if i.val < 3989 then
2389
else
2407)
else
(if i.val < 3991 then
2431
else
2452)))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
2453
else
2458)
else
(if i.val < 3995 then
2462
else
2472))
else
(if i.val < 3998 then
(if i.val < 3997 then
2473
else
2481)
else
(if i.val < 3999 then
2484
else
2493)))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
2495
else
2514)
else
(if i.val < 4003 then
2522
else
2527))
else
(if i.val < 4006 then
(if i.val < 4005 then
2532
else
2560)
else
(if i.val < 4007 then
2561
else
2574)))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
2578
else
2589)
else
(if i.val < 4011 then
2597
else
2607))
else
(if i.val < 4014 then
(if i.val < 4013 then
2614
else
2633)
else
(if i.val < 4015 then
2642
else
2643))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
2645
else
2646)
else
(if i.val < 4019 then
2647
else
2651))
else
(if i.val < 4022 then
(if i.val < 4021 then
2652
else
2661)
else
(if i.val < 4023 then
2662
else
2664)))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
2668
else
2676)
else
(if i.val < 4027 then
2677
else
2678))
else
(if i.val < 4030 then
(if i.val < 4029 then
2680
else
2688)
else
(if i.val < 4031 then
2689
else
2694))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
2698
else
2699)
else
(if i.val < 4035 then
2713
else
2730))
else
(if i.val < 4038 then
(if i.val < 4037 then
2747
else
2771)
else
(if i.val < 4039 then
2772
else
2774)))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
2780
else
2783)
else
(if i.val < 4043 then
2784
else
2785))
else
(if i.val < 4046 then
(if i.val < 4045 then
2790
else
2794)
else
(if i.val < 4047 then
2796
else
2798))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
2806
else
2813)
else
(if i.val < 4051 then
2822
else
2834))
else
(if i.val < 4054 then
(if i.val < 4053 then
2837
else
2846)
else
(if i.val < 4055 then
2850
else
2864)))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
2876
else
2885)
else
(if i.val < 4059 then
2886
else
2891))
else
(if i.val < 4062 then
(if i.val < 4061 then
2898
else
2906)
else
(if i.val < 4063 then
2911
else
2914)))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
2915
else
2945)
else
(if i.val < 4067 then
2947
else
2951))
else
(if i.val < 4070 then
(if i.val < 4069 then
2959
else
2965)
else
(if i.val < 4071 then
2971
else
2977)))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
2978
else
2986)
else
(if i.val < 4075 then
2998
else
3010))
else
(if i.val < 4078 then
(if i.val < 4077 then
3580
else
4218)
else
(if i.val < 4079 then
3800
else
4293))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
4284
else
4283)
else
(if i.val < 4083 then
4243
else
4290))
else
(if i.val < 4086 then
(if i.val < 4085 then
4271
else
3899)
else
(if i.val < 4087 then
3612
else
3723)))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
3860
else
4215)
else
(if i.val < 4091 then
4244
else
4294))
else
(if i.val < 4094 then
(if i.val < 4093 then
4295
else
3973)
else
(if i.val < 4095 then
4234
else
4209)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn0Part0008 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 4208 then
(if i.val < 4152 then
(if i.val < 4124 then
(if i.val < 4110 then
(if i.val < 4103 then
(if i.val < 4099 then
(if i.val < 4097 then
4296
else
(if i.val < 4098 then
4245
else
3977))
else
(if i.val < 4101 then
(if i.val < 4100 then
3701
else
3797)
else
(if i.val < 4102 then
4289
else
3948)))
else
(if i.val < 4106 then
(if i.val < 4104 then
4277
else
(if i.val < 4105 then
4221
else
4278))
else
(if i.val < 4108 then
(if i.val < 4107 then
3952
else
3609)
else
(if i.val < 4109 then
4247
else
4291))))
else
(if i.val < 4117 then
(if i.val < 4113 then
(if i.val < 4111 then
4240
else
(if i.val < 4112 then
4232
else
3900))
else
(if i.val < 4115 then
(if i.val < 4114 then
4239
else
4229)
else
(if i.val < 4116 then
4236
else
3607)))
else
(if i.val < 4120 then
(if i.val < 4118 then
3927
else
(if i.val < 4119 then
3845
else
4213))
else
(if i.val < 4122 then
(if i.val < 4121 then
4252
else
4256)
else
(if i.val < 4123 then
4279
else
3887)))))
else
(if i.val < 4138 then
(if i.val < 4131 then
(if i.val < 4127 then
(if i.val < 4125 then
4276
else
(if i.val < 4126 then
3886
else
4275))
else
(if i.val < 4129 then
(if i.val < 4128 then
3934
else
3935)
else
(if i.val < 4130 then
3970
else
3572)))
else
(if i.val < 4134 then
(if i.val < 4132 then
3693
else
(if i.val < 4133 then
3755
else
3865))
else
(if i.val < 4136 then
(if i.val < 4135 then
3702
else
3750)
else
(if i.val < 4137 then
3876
else
3873))))
else
(if i.val < 4145 then
(if i.val < 4141 then
(if i.val < 4139 then
4211
else
(if i.val < 4140 then
3711
else
3748))
else
(if i.val < 4143 then
(if i.val < 4142 then
4285
else
4230)
else
(if i.val < 4144 then
3894
else
4238)))
else
(if i.val < 4148 then
(if i.val < 4146 then
3846
else
(if i.val < 4147 then
4212
else
3805))
else
(if i.val < 4150 then
(if i.val < 4149 then
4286
else
4297)
else
(if i.val < 4151 then
4267
else
3617))))))
else
(if i.val < 4180 then
(if i.val < 4166 then
(if i.val < 4159 then
(if i.val < 4155 then
(if i.val < 4153 then
3712
else
(if i.val < 4154 then
4287
else
3774))
else
(if i.val < 4157 then
(if i.val < 4156 then
3961
else
3705)
else
(if i.val < 4158 then
3903
else
3802)))
else
(if i.val < 4162 then
(if i.val < 4160 then
4207
else
(if i.val < 4161 then
3732
else
4268))
else
(if i.val < 4164 then
(if i.val < 4163 then
3910
else
4269)
else
(if i.val < 4165 then
3795
else
4298))))
else
(if i.val < 4173 then
(if i.val < 4169 then
(if i.val < 4167 then
3858
else
(if i.val < 4168 then
4299
else
4270))
else
(if i.val < 4171 then
(if i.val < 4170 then
4300
else
4281)
else
(if i.val < 4172 then
4214
else
4231)))
else
(if i.val < 4176 then
(if i.val < 4174 then
3725
else
(if i.val < 4175 then
3885
else
3688))
else
(if i.val < 4178 then
(if i.val < 4177 then
3627
else
3964)
else
(if i.val < 4179 then
4261
else
4260)))))
else
(if i.val < 4194 then
(if i.val < 4187 then
(if i.val < 4183 then
(if i.val < 4181 then
4301
else
(if i.val < 4182 then
3966
else
3919))
else
(if i.val < 4185 then
(if i.val < 4184 then
4210
else
4228)
else
(if i.val < 4186 then
4302
else
3686)))
else
(if i.val < 4190 then
(if i.val < 4188 then
3772
else
(if i.val < 4189 then
4303
else
3597))
else
(if i.val < 4192 then
(if i.val < 4191 then
4304
else
3956)
else
(if i.val < 4193 then
3987
else
3895))))
else
(if i.val < 4201 then
(if i.val < 4197 then
(if i.val < 4195 then
3676
else
(if i.val < 4196 then
3644
else
3807))
else
(if i.val < 4199 then
(if i.val < 4198 then
3918
else
3631)
else
(if i.val < 4200 then
4223
else
3767)))
else
(if i.val < 4204 then
(if i.val < 4202 then
4305
else
(if i.val < 4203 then
4246
else
3613))
else
(if i.val < 4206 then
(if i.val < 4205 then
3668
else
4216)
else
(if i.val < 4207 then
4242
else
3828)))))))
else
(if i.val < 4264 then
(if i.val < 4236 then
(if i.val < 4222 then
(if i.val < 4215 then
(if i.val < 4211 then
(if i.val < 4209 then
4226
else
(if i.val < 4210 then
3649
else
3929))
else
(if i.val < 4213 then
(if i.val < 4212 then
3766
else
3781)
else
(if i.val < 4214 then
3722
else
3897)))
else
(if i.val < 4218 then
(if i.val < 4216 then
3623
else
(if i.val < 4217 then
3986
else
4280))
else
(if i.val < 4220 then
(if i.val < 4219 then
3578
else
4282)
else
(if i.val < 4221 then
4217
else
3681))))
else
(if i.val < 4229 then
(if i.val < 4225 then
(if i.val < 4223 then
4306
else
(if i.val < 4224 then
3968
else
4307))
else
(if i.val < 4227 then
(if i.val < 4226 then
4308
else
4253)
else
(if i.val < 4228 then
4251
else
3936)))
else
(if i.val < 4232 then
(if i.val < 4230 then
3715
else
(if i.val < 4231 then
3776
else
3901))
else
(if i.val < 4234 then
(if i.val < 4233 then
3707
else
4241)
else
(if i.val < 4235 then
3648
else
4309)))))
else
(if i.val < 4250 then
(if i.val < 4243 then
(if i.val < 4239 then
(if i.val < 4237 then
3716
else
(if i.val < 4238 then
4265
else
3779))
else
(if i.val < 4241 then
(if i.val < 4240 then
3713
else
3703)
else
(if i.val < 4242 then
4266
else
4310)))
else
(if i.val < 4246 then
(if i.val < 4244 then
3599
else
(if i.val < 4245 then
3625
else
3669))
else
(if i.val < 4248 then
(if i.val < 4247 then
3974
else
3687)
else
(if i.val < 4249 then
4311
else
4219))))
else
(if i.val < 4257 then
(if i.val < 4253 then
(if i.val < 4251 then
4312
else
(if i.val < 4252 then
4313
else
3724))
else
(if i.val < 4255 then
(if i.val < 4254 then
4208
else
4258)
else
(if i.val < 4256 then
4314
else
3726)))
else
(if i.val < 4260 then
(if i.val < 4258 then
4224
else
(if i.val < 4259 then
4315
else
4250))
else
(if i.val < 4262 then
(if i.val < 4261 then
3921
else
3920)
else
(if i.val < 4263 then
4274
else
4248))))))
else
(if i.val < 4292 then
(if i.val < 4278 then
(if i.val < 4271 then
(if i.val < 4267 then
(if i.val < 4265 then
4292
else
(if i.val < 4266 then
4316
else
4233))
else
(if i.val < 4269 then
(if i.val < 4268 then
3790
else
3833)
else
(if i.val < 4270 then
3857
else
3882)))
else
(if i.val < 4274 then
(if i.val < 4272 then
3608
else
(if i.val < 4273 then
4262
else
4225))
else
(if i.val < 4276 then
(if i.val < 4275 then
4272
else
3735)
else
(if i.val < 4277 then
3733
else
3680))))
else
(if i.val < 4285 then
(if i.val < 4281 then
(if i.val < 4279 then
3682
else
(if i.val < 4280 then
3727
else
4220))
else
(if i.val < 4283 then
(if i.val < 4282 then
3893
else
4249)
else
(if i.val < 4284 then
3590
else
3589)))
else
(if i.val < 4288 then
(if i.val < 4286 then
3773
else
(if i.val < 4287 then
3786
else
3793))
else
(if i.val < 4290 then
(if i.val < 4289 then
4235
else
3675)
else
(if i.val < 4291 then
3603
else
3698)))))
else
(if i.val < 4306 then
(if i.val < 4299 then
(if i.val < 4295 then
(if i.val < 4293 then
4317
else
(if i.val < 4294 then
3587
else
3632))
else
(if i.val < 4297 then
(if i.val < 4296 then
3640
else
3666)
else
(if i.val < 4298 then
3787
else
3863)))
else
(if i.val < 4302 then
(if i.val < 4300 then
3872
else
(if i.val < 4301 then
3892
else
3923))
else
(if i.val < 4304 then
(if i.val < 4303 then
3937
else
3945)
else
(if i.val < 4305 then
3951
else
3972))))
else
(if i.val < 4313 then
(if i.val < 4309 then
(if i.val < 4307 then
4319
else
(if i.val < 4308 then
4257
else
4273))
else
(if i.val < 4311 then
(if i.val < 4310 then
4288
else
4206)
else
(if i.val < 4312 then
4263
else
4259)))
else
(if i.val < 4316 then
(if i.val < 4314 then
4227
else
(if i.val < 4315 then
4318
else
4254))
else
(if i.val < 4318 then
(if i.val < 4317 then
4237
else
4264)
else
(if i.val < 4319 then
4255
else
4222))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0000 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 256 then
(if i.val < 128 then
(if i.val < 64 then
(if i.val < 32 then
(if i.val < 16 then
(if i.val < 8 then
(if i.val < 4 then
(if i.val < 2 then
(if i.val < 1 then
2
else
9)
else
(if i.val < 3 then
10
else
11))
else
(if i.val < 6 then
(if i.val < 5 then
12
else
32)
else
(if i.val < 7 then
22
else
33)))
else
(if i.val < 12 then
(if i.val < 10 then
(if i.val < 9 then
34
else
35)
else
(if i.val < 11 then
0
else
36))
else
(if i.val < 14 then
(if i.val < 13 then
37
else
38)
else
(if i.val < 15 then
39
else
40))))
else
(if i.val < 24 then
(if i.val < 20 then
(if i.val < 18 then
(if i.val < 17 then
41
else
42)
else
(if i.val < 19 then
43
else
57))
else
(if i.val < 22 then
(if i.val < 21 then
96
else
97)
else
(if i.val < 23 then
69
else
59)))
else
(if i.val < 28 then
(if i.val < 26 then
(if i.val < 25 then
70
else
71)
else
(if i.val < 27 then
98
else
99))
else
(if i.val < 30 then
(if i.val < 29 then
100
else
101)
else
(if i.val < 31 then
102
else
103)))))
else
(if i.val < 48 then
(if i.val < 40 then
(if i.val < 36 then
(if i.val < 34 then
(if i.val < 33 then
104
else
105)
else
(if i.val < 35 then
106
else
1))
else
(if i.val < 38 then
(if i.val < 37 then
3
else
4)
else
(if i.val < 39 then
107
else
108)))
else
(if i.val < 44 then
(if i.val < 42 then
(if i.val < 41 then
109
else
110)
else
(if i.val < 43 then
111
else
112))
else
(if i.val < 46 then
(if i.val < 45 then
113
else
114)
else
(if i.val < 47 then
115
else
116))))
else
(if i.val < 56 then
(if i.val < 52 then
(if i.val < 50 then
(if i.val < 49 then
117
else
118)
else
(if i.val < 51 then
85
else
119))
else
(if i.val < 54 then
(if i.val < 53 then
120
else
121)
else
(if i.val < 55 then
122
else
123)))
else
(if i.val < 60 then
(if i.val < 58 then
(if i.val < 57 then
124
else
125)
else
(if i.val < 59 then
126
else
94))
else
(if i.val < 62 then
(if i.val < 61 then
166
else
255)
else
(if i.val < 63 then
256
else
257))))))
else
(if i.val < 96 then
(if i.val < 80 then
(if i.val < 72 then
(if i.val < 68 then
(if i.val < 66 then
(if i.val < 65 then
258
else
259)
else
(if i.val < 67 then
203
else
260))
else
(if i.val < 70 then
(if i.val < 69 then
90
else
6)
else
(if i.val < 71 then
190
else
191)))
else
(if i.val < 76 then
(if i.val < 74 then
(if i.val < 73 then
163
else
164)
else
(if i.val < 75 then
165
else
192))
else
(if i.val < 78 then
(if i.val < 77 then
193
else
194)
else
(if i.val < 79 then
195
else
196))))
else
(if i.val < 88 then
(if i.val < 84 then
(if i.val < 82 then
(if i.val < 81 then
197
else
261)
else
(if i.val < 83 then
262
else
263))
else
(if i.val < 86 then
(if i.val < 85 then
264
else
265)
else
(if i.val < 87 then
266
else
267)))
else
(if i.val < 92 then
(if i.val < 90 then
(if i.val < 89 then
268
else
269)
else
(if i.val < 91 then
270
else
271))
else
(if i.val < 94 then
(if i.val < 93 then
272
else
273)
else
(if i.val < 95 then
23
else
274)))))
else
(if i.val < 112 then
(if i.val < 104 then
(if i.val < 100 then
(if i.val < 98 then
(if i.val < 97 then
275
else
148)
else
(if i.val < 99 then
276
else
277))
else
(if i.val < 102 then
(if i.val < 101 then
278
else
172)
else
(if i.val < 103 then
279
else
280)))
else
(if i.val < 108 then
(if i.val < 106 then
(if i.val < 105 then
5
else
7)
else
(if i.val < 107 then
8
else
13))
else
(if i.val < 110 then
(if i.val < 109 then
14
else
15)
else
(if i.val < 111 then
16
else
17))))
else
(if i.val < 120 then
(if i.val < 116 then
(if i.val < 114 then
(if i.val < 113 then
18
else
281)
else
(if i.val < 115 then
282
else
283))
else
(if i.val < 118 then
(if i.val < 117 then
284
else
285)
else
(if i.val < 119 then
286
else
287)))
else
(if i.val < 124 then
(if i.val < 122 then
(if i.val < 121 then
288
else
289)
else
(if i.val < 123 then
290
else
291))
else
(if i.val < 126 then
(if i.val < 125 then
292
else
19)
else
(if i.val < 127 then
293
else
294)))))))
else
(if i.val < 192 then
(if i.val < 160 then
(if i.val < 144 then
(if i.val < 136 then
(if i.val < 132 then
(if i.val < 130 then
(if i.val < 129 then
295
else
296)
else
(if i.val < 131 then
297
else
298))
else
(if i.val < 134 then
(if i.val < 133 then
299
else
300)
else
(if i.val < 135 then
301
else
302)))
else
(if i.val < 140 then
(if i.val < 138 then
(if i.val < 137 then
303
else
304)
else
(if i.val < 139 then
305
else
306))
else
(if i.val < 142 then
(if i.val < 141 then
307
else
308)
else
(if i.val < 143 then
309
else
230))))
else
(if i.val < 152 then
(if i.val < 148 then
(if i.val < 146 then
(if i.val < 145 then
310
else
311)
else
(if i.val < 147 then
312
else
84))
else
(if i.val < 150 then
(if i.val < 149 then
21
else
313)
else
(if i.val < 151 then
314
else
315)))
else
(if i.val < 156 then
(if i.val < 154 then
(if i.val < 153 then
316
else
317)
else
(if i.val < 155 then
318
else
319))
else
(if i.val < 158 then
(if i.val < 157 then
320
else
321)
else
(if i.val < 159 then
322
else
323)))))
else
(if i.val < 176 then
(if i.val < 168 then
(if i.val < 164 then
(if i.val < 162 then
(if i.val < 161 then
324
else
325)
else
(if i.val < 163 then
326
else
188))
else
(if i.val < 166 then
(if i.val < 165 then
460
else
461)
else
(if i.val < 167 then
218
else
407)))
else
(if i.val < 172 then
(if i.val < 170 then
(if i.val < 169 then
408
else
596)
else
(if i.val < 171 then
597
else
598))
else
(if i.val < 174 then
(if i.val < 173 then
29
else
599)
else
(if i.val < 175 then
214
else
600))))
else
(if i.val < 184 then
(if i.val < 180 then
(if i.val < 178 then
(if i.val < 177 then
601
else
602)
else
(if i.val < 179 then
603
else
472))
else
(if i.val < 182 then
(if i.val < 181 then
604
else
605)
else
(if i.val < 183 then
606
else
149)))
else
(if i.val < 188 then
(if i.val < 186 then
(if i.val < 185 then
80
else
607)
else
(if i.val < 187 then
608
else
609))
else
(if i.val < 190 then
(if i.val < 189 then
72
else
610)
else
(if i.val < 191 then
24
else
25))))))
else
(if i.val < 224 then
(if i.val < 208 then
(if i.val < 200 then
(if i.val < 196 then
(if i.val < 194 then
(if i.val < 193 then
462
else
463)
else
(if i.val < 195 then
464
else
412))
else
(if i.val < 198 then
(if i.val < 197 then
465
else
184)
else
(if i.val < 199 then
400
else
158)))
else
(if i.val < 204 then
(if i.val < 202 then
(if i.val < 201 then
401
else
402)
else
(if i.val < 203 then
403
else
404))
else
(if i.val < 206 then
(if i.val < 205 then
405
else
406)
else
(if i.val < 207 then
466
else
467))))
else
(if i.val < 216 then
(if i.val < 212 then
(if i.val < 210 then
(if i.val < 209 then
468
else
469)
else
(if i.val < 211 then
470
else
471))
else
(if i.val < 214 then
(if i.val < 213 then
473
else
474)
else
(if i.val < 215 then
475
else
476)))
else
(if i.val < 220 then
(if i.val < 218 then
(if i.val < 217 then
477
else
478)
else
(if i.val < 219 then
60
else
479))
else
(if i.val < 222 then
(if i.val < 221 then
611
else
612)
else
(if i.val < 223 then
613
else
614)))))
else
(if i.val < 240 then
(if i.val < 232 then
(if i.val < 228 then
(if i.val < 226 then
(if i.val < 225 then
615
else
162)
else
(if i.val < 227 then
616
else
617))
else
(if i.val < 230 then
(if i.val < 229 then
618
else
619)
else
(if i.val < 231 then
620
else
621)))
else
(if i.val < 236 then
(if i.val < 234 then
(if i.val < 233 then
622
else
623)
else
(if i.val < 235 then
624
else
625))
else
(if i.val < 238 then
(if i.val < 237 then
626
else
627)
else
(if i.val < 239 then
628
else
629))))
else
(if i.val < 248 then
(if i.val < 244 then
(if i.val < 242 then
(if i.val < 241 then
630
else
62)
else
(if i.val < 243 then
213
else
631))
else
(if i.val < 246 then
(if i.val < 245 then
632
else
633)
else
(if i.val < 247 then
634
else
635)))
else
(if i.val < 252 then
(if i.val < 250 then
(if i.val < 249 then
636
else
637)
else
(if i.val < 251 then
638
else
639))
else
(if i.val < 254 then
(if i.val < 253 then
640
else
641)
else
(if i.val < 255 then
642
else
480))))))))
else
(if i.val < 384 then
(if i.val < 320 then
(if i.val < 288 then
(if i.val < 272 then
(if i.val < 264 then
(if i.val < 260 then
(if i.val < 258 then
(if i.val < 257 then
241
else
643)
else
(if i.val < 259 then
381
else
644))
else
(if i.val < 262 then
(if i.val < 261 then
645
else
573)
else
(if i.val < 263 then
646
else
647)))
else
(if i.val < 268 then
(if i.val < 266 then
(if i.val < 265 then
147
else
50)
else
(if i.val < 267 then
648
else
649))
else
(if i.val < 270 then
(if i.val < 269 then
650
else
651)
else
(if i.val < 271 then
68
else
652))))
else
(if i.val < 280 then
(if i.val < 276 then
(if i.val < 274 then
(if i.val < 273 then
653
else
654)
else
(if i.val < 275 then
655
else
20))
else
(if i.val < 278 then
(if i.val < 277 then
26
else
27)
else
(if i.val < 279 then
28
else
30)))
else
(if i.val < 284 then
(if i.val < 282 then
(if i.val < 281 then
31
else
44)
else
(if i.val < 283 then
45
else
46))
else
(if i.val < 286 then
(if i.val < 285 then
47
else
48)
else
(if i.val < 287 then
49
else
51)))))
else
(if i.val < 304 then
(if i.val < 296 then
(if i.val < 292 then
(if i.val < 290 then
(if i.val < 289 then
52
else
53)
else
(if i.val < 291 then
54
else
55))
else
(if i.val < 294 then
(if i.val < 293 then
56
else
58)
else
(if i.val < 295 then
656
else
657)))
else
(if i.val < 300 then
(if i.val < 298 then
(if i.val < 297 then
658
else
659)
else
(if i.val < 299 then
660
else
661))
else
(if i.val < 302 then
(if i.val < 301 then
662
else
663)
else
(if i.val < 303 then
664
else
665))))
else
(if i.val < 312 then
(if i.val < 308 then
(if i.val < 306 then
(if i.val < 305 then
666
else
667)
else
(if i.val < 307 then
668
else
669))
else
(if i.val < 310 then
(if i.val < 309 then
670
else
671)
else
(if i.val < 311 then
672
else
673)))
else
(if i.val < 316 then
(if i.val < 314 then
(if i.val < 313 then
674
else
183)
else
(if i.val < 315 then
675
else
676))
else
(if i.val < 318 then
(if i.val < 317 then
677
else
678)
else
(if i.val < 319 then
679
else
680))))))
else
(if i.val < 352 then
(if i.val < 336 then
(if i.val < 328 then
(if i.val < 324 then
(if i.val < 322 then
(if i.val < 321 then
681
else
682)
else
(if i.val < 323 then
199
else
683))
else
(if i.val < 326 then
(if i.val < 325 then
684
else
685)
else
(if i.val < 327 then
225
else
686)))
else
(if i.val < 332 then
(if i.val < 330 then
(if i.val < 329 then
687
else
688)
else
(if i.val < 331 then
689
else
690))
else
(if i.val < 334 then
(if i.val < 333 then
691
else
692)
else
(if i.val < 335 then
693
else
694))))
else
(if i.val < 344 then
(if i.val < 340 then
(if i.val < 338 then
(if i.val < 337 then
695
else
696)
else
(if i.val < 339 then
697
else
492))
else
(if i.val < 342 then
(if i.val < 341 then
698
else
699)
else
(if i.val < 343 then
700
else
701)))
else
(if i.val < 348 then
(if i.val < 346 then
(if i.val < 345 then
702
else
703)
else
(if i.val < 347 then
704
else
705))
else
(if i.val < 350 then
(if i.val < 349 then
706
else
707)
else
(if i.val < 351 then
708
else
709)))))
else
(if i.val < 368 then
(if i.val < 360 then
(if i.val < 356 then
(if i.val < 354 then
(if i.val < 353 then
710
else
711)
else
(if i.val < 355 then
227
else
712))
else
(if i.val < 358 then
(if i.val < 357 then
713
else
714)
else
(if i.val < 359 then
545
else
715)))
else
(if i.val < 364 then
(if i.val < 362 then
(if i.val < 361 then
716
else
717)
else
(if i.val < 363 then
544
else
718))
else
(if i.val < 366 then
(if i.val < 365 then
719
else
720)
else
(if i.val < 367 then
721
else
722))))
else
(if i.val < 376 then
(if i.val < 372 then
(if i.val < 370 then
(if i.val < 369 then
723
else
724)
else
(if i.val < 371 then
725
else
726))
else
(if i.val < 374 then
(if i.val < 373 then
727
else
728)
else
(if i.val < 375 then
729
else
730)))
else
(if i.val < 380 then
(if i.val < 378 then
(if i.val < 377 then
731
else
732)
else
(if i.val < 379 then
733
else
734))
else
(if i.val < 382 then
(if i.val < 381 then
735
else
64)
else
(if i.val < 383 then
538
else
519)))))))
else
(if i.val < 448 then
(if i.val < 416 then
(if i.val < 400 then
(if i.val < 392 then
(if i.val < 388 then
(if i.val < 386 then
(if i.val < 385 then
348
else
423)
else
(if i.val < 387 then
736
else
737))
else
(if i.val < 390 then
(if i.val < 389 then
738
else
739)
else
(if i.val < 391 then
740
else
741)))
else
(if i.val < 396 then
(if i.val < 394 then
(if i.val < 393 then
382
else
742)
else
(if i.val < 395 then
743
else
744))
else
(if i.val < 398 then
(if i.val < 397 then
745
else
746)
else
(if i.val < 399 then
747
else
748))))
else
(if i.val < 408 then
(if i.val < 404 then
(if i.val < 402 then
(if i.val < 401 then
899
else
1015)
else
(if i.val < 403 then
1016
else
1017))
else
(if i.val < 406 then
(if i.val < 405 then
66
else
1018)
else
(if i.val < 407 then
422
else
917)))
else
(if i.val < 412 then
(if i.val < 410 then
(if i.val < 409 then
446
else
918)
else
(if i.val < 411 then
919
else
920))
else
(if i.val < 414 then
(if i.val < 413 then
78
else
921)
else
(if i.val < 415 then
1282
else
1283)))))
else
(if i.val < 432 then
(if i.val < 424 then
(if i.val < 420 then
(if i.val < 418 then
(if i.val < 417 then
1284
else
1285)
else
(if i.val < 419 then
1062
else
1286))
else
(if i.val < 422 then
(if i.val < 421 then
1287
else
456)
else
(if i.val < 423 then
205
else
1288)))
else
(if i.val < 428 then
(if i.val < 426 then
(if i.val < 425 then
1289
else
1290)
else
(if i.val < 427 then
857
else
1291))
else
(if i.val < 430 then
(if i.val < 429 then
1292
else
1293)
else
(if i.val < 431 then
1294
else
1295))))
else
(if i.val < 440 then
(if i.val < 436 then
(if i.val < 434 then
(if i.val < 433 then
1296
else
1297)
else
(if i.val < 435 then
1298
else
1299))
else
(if i.val < 438 then
(if i.val < 437 then
1044
else
1300)
else
(if i.val < 439 then
1301
else
1302)))
else
(if i.val < 444 then
(if i.val < 442 then
(if i.val < 441 then
1303
else
1304)
else
(if i.val < 443 then
1305
else
566))
else
(if i.val < 446 then
(if i.val < 445 then
1306
else
1307)
else
(if i.val < 447 then
168
else
251))))))
else
(if i.val < 480 then
(if i.val < 464 then
(if i.val < 456 then
(if i.val < 452 then
(if i.val < 450 then
(if i.val < 449 then
1308
else
1309)
else
(if i.val < 451 then
1310
else
1311))
else
(if i.val < 454 then
(if i.val < 453 then
1000
else
1312)
else
(if i.val < 455 then
1313
else
1314)))
else
(if i.val < 460 then
(if i.val < 458 then
(if i.val < 457 then
516
else
1315)
else
(if i.val < 459 then
1316
else
1317))
else
(if i.val < 462 then
(if i.val < 461 then
73
else
74)
else
(if i.val < 463 then
75
else
76))))
else
(if i.val < 472 then
(if i.val < 468 then
(if i.val < 466 then
(if i.val < 465 then
77
else
79)
else
(if i.val < 467 then
1019
else
1020))
else
(if i.val < 470 then
(if i.val < 469 then
1021
else
1022)
else
(if i.val < 471 then
910
else
1023)))
else
(if i.val < 476 then
(if i.val < 474 then
(if i.val < 473 then
864
else
1024)
else
(if i.val < 475 then
242
else
174))
else
(if i.val < 478 then
(if i.val < 477 then
1025
else
1026)
else
(if i.val < 479 then
1027
else
1028)))))
else
(if i.val < 496 then
(if i.val < 488 then
(if i.val < 484 then
(if i.val < 482 then
(if i.val < 481 then
61
else
900)
else
(if i.val < 483 then
901
else
902))
else
(if i.val < 486 then
(if i.val < 485 then
903
else
904)
else
(if i.val < 487 then
905
else
906)))
else
(if i.val < 492 then
(if i.val < 490 then
(if i.val < 489 then
907
else
908)
else
(if i.val < 491 then
909
else
911))
else
(if i.val < 494 then
(if i.val < 493 then
912
else
913)
else
(if i.val < 495 then
914
else
915))))
else
(if i.val < 504 then
(if i.val < 500 then
(if i.val < 498 then
(if i.val < 497 then
916
else
1029)
else
(if i.val < 499 then
1030
else
1031))
else
(if i.val < 502 then
(if i.val < 501 then
1032
else
1033)
else
(if i.val < 503 then
254
else
1034)))
else
(if i.val < 508 then
(if i.val < 506 then
(if i.val < 505 then
1035
else
1036)
else
(if i.val < 507 then
1037
else
1038))
else
(if i.val < 510 then
(if i.val < 509 then
1039
else
1040)
else
(if i.val < 511 then
1041
else
1042)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0001 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 768 then
(if i.val < 640 then
(if i.val < 576 then
(if i.val < 544 then
(if i.val < 528 then
(if i.val < 520 then
(if i.val < 516 then
(if i.val < 514 then
(if i.val < 513 then
1043
else
1045)
else
(if i.val < 515 then
1046
else
1047))
else
(if i.val < 518 then
(if i.val < 517 then
421
else
1048)
else
(if i.val < 519 then
1049
else
1050)))
else
(if i.val < 524 then
(if i.val < 522 then
(if i.val < 521 then
1051
else
826)
else
(if i.val < 523 then
1052
else
1053))
else
(if i.val < 526 then
(if i.val < 525 then
1054
else
1055)
else
(if i.val < 527 then
1056
else
1318))))
else
(if i.val < 536 then
(if i.val < 532 then
(if i.val < 530 then
(if i.val < 529 then
369
else
365)
else
(if i.val < 531 then
1319
else
1320))
else
(if i.val < 534 then
(if i.val < 533 then
1321
else
1322)
else
(if i.val < 535 then
1323
else
1324)))
else
(if i.val < 540 then
(if i.val < 538 then
(if i.val < 537 then
395
else
399)
else
(if i.val < 539 then
392
else
1325))
else
(if i.val < 542 then
(if i.val < 541 then
1326
else
1327)
else
(if i.val < 543 then
1328
else
1329)))))
else
(if i.val < 560 then
(if i.val < 552 then
(if i.val < 548 then
(if i.val < 546 then
(if i.val < 545 then
1330
else
1331)
else
(if i.val < 547 then
1332
else
1333))
else
(if i.val < 550 then
(if i.val < 549 then
1334
else
1335)
else
(if i.val < 551 then
1336
else
1337)))
else
(if i.val < 556 then
(if i.val < 554 then
(if i.val < 553 then
1338
else
1339)
else
(if i.val < 555 then
1340
else
1341))
else
(if i.val < 558 then
(if i.val < 557 then
1342
else
1343)
else
(if i.val < 559 then
1344
else
1345))))
else
(if i.val < 568 then
(if i.val < 564 then
(if i.val < 562 then
(if i.val < 561 then
1211
else
1087)
else
(if i.val < 563 then
1346
else
1347))
else
(if i.val < 566 then
(if i.val < 565 then
1348
else
1349)
else
(if i.val < 567 then
1350
else
1351)))
else
(if i.val < 572 then
(if i.val < 570 then
(if i.val < 569 then
1013
else
1352)
else
(if i.val < 571 then
1353
else
1354))
else
(if i.val < 574 then
(if i.val < 573 then
1355
else
81)
else
(if i.val < 575 then
1356
else
1357))))))
else
(if i.val < 608 then
(if i.val < 592 then
(if i.val < 584 then
(if i.val < 580 then
(if i.val < 578 then
(if i.val < 577 then
1358
else
170)
else
(if i.val < 579 then
1359
else
1360))
else
(if i.val < 582 then
(if i.val < 581 then
1361
else
928)
else
(if i.val < 583 then
1362
else
1363)))
else
(if i.val < 588 then
(if i.val < 586 then
(if i.val < 585 then
1364
else
771)
else
(if i.val < 587 then
1365
else
965))
else
(if i.val < 590 then
(if i.val < 589 then
1366
else
1367)
else
(if i.val < 591 then
1368
else
1369))))
else
(if i.val < 600 then
(if i.val < 596 then
(if i.val < 594 then
(if i.val < 593 then
1370
else
1371)
else
(if i.val < 595 then
1372
else
1373))
else
(if i.val < 598 then
(if i.val < 597 then
1057
else
577)
else
(if i.val < 599 then
1058
else
819)))
else
(if i.val < 604 then
(if i.val < 602 then
(if i.val < 601 then
1136
else
1374)
else
(if i.val < 603 then
1375
else
863))
else
(if i.val < 606 then
(if i.val < 605 then
1376
else
926)
else
(if i.val < 607 then
1377
else
1002)))))
else
(if i.val < 624 then
(if i.val < 616 then
(if i.val < 612 then
(if i.val < 610 then
(if i.val < 609 then
1378
else
854)
else
(if i.val < 611 then
1264
else
1379))
else
(if i.val < 614 then
(if i.val < 613 then
1380
else
1381)
else
(if i.val < 615 then
1382
else
1383)))
else
(if i.val < 620 then
(if i.val < 618 then
(if i.val < 617 then
1384
else
354)
else
(if i.val < 619 then
873
else
1385))
else
(if i.val < 622 then
(if i.val < 621 then
143
else
1198)
else
(if i.val < 623 then
1386
else
1387))))
else
(if i.val < 632 then
(if i.val < 628 then
(if i.val < 626 then
(if i.val < 625 then
1388
else
1389)
else
(if i.val < 627 then
1390
else
1391))
else
(if i.val < 630 then
(if i.val < 629 then
1392
else
1393)
else
(if i.val < 631 then
1394
else
1395)))
else
(if i.val < 636 then
(if i.val < 634 then
(if i.val < 633 then
1396
else
1397)
else
(if i.val < 635 then
1398
else
1399))
else
(if i.val < 638 then
(if i.val < 637 then
1400
else
1401)
else
(if i.val < 639 then
1402
else
447)))))))
else
(if i.val < 704 then
(if i.val < 672 then
(if i.val < 656 then
(if i.val < 648 then
(if i.val < 644 then
(if i.val < 642 then
(if i.val < 641 then
1403
else
1404)
else
(if i.val < 643 then
502
else
63))
else
(if i.val < 646 then
(if i.val < 645 then
65
else
67)
else
(if i.val < 647 then
82
else
83)))
else
(if i.val < 652 then
(if i.val < 650 then
(if i.val < 649 then
86
else
87)
else
(if i.val < 651 then
88
else
89))
else
(if i.val < 654 then
(if i.val < 653 then
91
else
92)
else
(if i.val < 655 then
93
else
95))))
else
(if i.val < 664 then
(if i.val < 660 then
(if i.val < 658 then
(if i.val < 657 then
127
else
128)
else
(if i.val < 659 then
129
else
130))
else
(if i.val < 662 then
(if i.val < 661 then
131
else
132)
else
(if i.val < 663 then
133
else
134)))
else
(if i.val < 668 then
(if i.val < 666 then
(if i.val < 665 then
135
else
136)
else
(if i.val < 667 then
137
else
138))
else
(if i.val < 670 then
(if i.val < 669 then
139
else
140)
else
(if i.val < 671 then
141
else
142)))))
else
(if i.val < 688 then
(if i.val < 680 then
(if i.val < 676 then
(if i.val < 674 then
(if i.val < 673 then
144
else
145)
else
(if i.val < 675 then
146
else
150))
else
(if i.val < 678 then
(if i.val < 677 then
151
else
152)
else
(if i.val < 679 then
153
else
154)))
else
(if i.val < 684 then
(if i.val < 682 then
(if i.val < 681 then
155
else
156)
else
(if i.val < 683 then
157
else
159))
else
(if i.val < 686 then
(if i.val < 685 then
160
else
161)
else
(if i.val < 687 then
1096
else
1405))))
else
(if i.val < 696 then
(if i.val < 692 then
(if i.val < 690 then
(if i.val < 689 then
1406
else
1407)
else
(if i.val < 691 then
1408
else
875))
else
(if i.val < 694 then
(if i.val < 693 then
1409
else
1410)
else
(if i.val < 695 then
1153
else
1411)))
else
(if i.val < 700 then
(if i.val < 698 then
(if i.val < 697 then
1412
else
1413)
else
(if i.val < 699 then
1414
else
1415))
else
(if i.val < 702 then
(if i.val < 701 then
1140
else
817)
else
(if i.val < 703 then
1416
else
1417))))))
else
(if i.val < 736 then
(if i.val < 720 then
(if i.val < 712 then
(if i.val < 708 then
(if i.val < 706 then
(if i.val < 705 then
1418
else
860)
else
(if i.val < 707 then
384
else
1419))
else
(if i.val < 710 then
(if i.val < 709 then
1420
else
1421)
else
(if i.val < 711 then
1422
else
1423)))
else
(if i.val < 716 then
(if i.val < 714 then
(if i.val < 713 then
1424
else
1425)
else
(if i.val < 715 then
1193
else
1426))
else
(if i.val < 718 then
(if i.val < 717 then
1427
else
1428)
else
(if i.val < 719 then
1429
else
949))))
else
(if i.val < 728 then
(if i.val < 724 then
(if i.val < 722 then
(if i.val < 721 then
529
else
1430)
else
(if i.val < 723 then
832
else
1431))
else
(if i.val < 726 then
(if i.val < 725 then
528
else
1432)
else
(if i.val < 727 then
1433
else
891)))
else
(if i.val < 732 then
(if i.val < 730 then
(if i.val < 729 then
1434
else
1435)
else
(if i.val < 731 then
1436
else
1437))
else
(if i.val < 734 then
(if i.val < 733 then
922
else
1438)
else
(if i.val < 735 then
1224
else
1439)))))
else
(if i.val < 752 then
(if i.val < 744 then
(if i.val < 740 then
(if i.val < 738 then
(if i.val < 737 then
1440
else
1441)
else
(if i.val < 739 then
1442
else
1443))
else
(if i.val < 742 then
(if i.val < 741 then
1444
else
1445)
else
(if i.val < 743 then
1446
else
1447)))
else
(if i.val < 748 then
(if i.val < 746 then
(if i.val < 745 then
536
else
1448)
else
(if i.val < 747 then
1133
else
1139))
else
(if i.val < 750 then
(if i.val < 749 then
537
else
1449)
else
(if i.val < 751 then
1450
else
1451))))
else
(if i.val < 760 then
(if i.val < 756 then
(if i.val < 754 then
(if i.val < 753 then
1452
else
1453)
else
(if i.val < 755 then
1454
else
1235))
else
(if i.val < 758 then
(if i.val < 757 then
1455
else
1456)
else
(if i.val < 759 then
1457
else
1201)))
else
(if i.val < 764 then
(if i.val < 762 then
(if i.val < 761 then
1458
else
1459)
else
(if i.val < 763 then
1460
else
1461))
else
(if i.val < 766 then
(if i.val < 765 then
1462
else
1463)
else
(if i.val < 767 then
1464
else
1162))))))))
else
(if i.val < 896 then
(if i.val < 832 then
(if i.val < 800 then
(if i.val < 784 then
(if i.val < 776 then
(if i.val < 772 then
(if i.val < 770 then
(if i.val < 769 then
1465
else
1466)
else
(if i.val < 771 then
1467
else
1468))
else
(if i.val < 774 then
(if i.val < 773 then
1469
else
1470)
else
(if i.val < 775 then
1471
else
1472)))
else
(if i.val < 780 then
(if i.val < 778 then
(if i.val < 777 then
1473
else
843)
else
(if i.val < 779 then
1239
else
1474))
else
(if i.val < 782 then
(if i.val < 781 then
1475
else
1476)
else
(if i.val < 783 then
1477
else
1478))))
else
(if i.val < 792 then
(if i.val < 788 then
(if i.val < 786 then
(if i.val < 785 then
1479
else
1480)
else
(if i.val < 787 then
1481
else
1482))
else
(if i.val < 790 then
(if i.val < 789 then
1483
else
1484)
else
(if i.val < 791 then
1485
else
541)))
else
(if i.val < 796 then
(if i.val < 794 then
(if i.val < 793 then
1486
else
1487)
else
(if i.val < 795 then
1488
else
1115))
else
(if i.val < 798 then
(if i.val < 797 then
1489
else
1180)
else
(if i.val < 799 then
1490
else
1491)))))
else
(if i.val < 816 then
(if i.val < 808 then
(if i.val < 804 then
(if i.val < 802 then
(if i.val < 801 then
1492
else
1493)
else
(if i.val < 803 then
1494
else
1495))
else
(if i.val < 806 then
(if i.val < 805 then
1496
else
1497)
else
(if i.val < 807 then
1498
else
1499)))
else
(if i.val < 812 then
(if i.val < 810 then
(if i.val < 809 then
865
else
1500)
else
(if i.val < 811 then
558
else
1501))
else
(if i.val < 814 then
(if i.val < 813 then
1502
else
1503)
else
(if i.val < 815 then
1504
else
542))))
else
(if i.val < 824 then
(if i.val < 820 then
(if i.val < 818 then
(if i.val < 817 then
1178
else
343)
else
(if i.val < 819 then
1505
else
173))
else
(if i.val < 822 then
(if i.val < 821 then
786
else
1506)
else
(if i.val < 823 then
1177
else
1507)))
else
(if i.val < 828 then
(if i.val < 826 then
(if i.val < 825 then
1508
else
1509)
else
(if i.val < 827 then
1510
else
1511))
else
(if i.val < 830 then
(if i.val < 829 then
1512
else
1184)
else
(if i.val < 831 then
1513
else
1514))))))
else
(if i.val < 864 then
(if i.val < 848 then
(if i.val < 840 then
(if i.val < 836 then
(if i.val < 834 then
(if i.val < 833 then
367
else
1515)
else
(if i.val < 835 then
1516
else
1517))
else
(if i.val < 838 then
(if i.val < 837 then
1518
else
1519)
else
(if i.val < 839 then
1520
else
1521)))
else
(if i.val < 844 then
(if i.val < 842 then
(if i.val < 841 then
1522
else
1183)
else
(if i.val < 843 then
549
else
1523))
else
(if i.val < 846 then
(if i.val < 845 then
1524
else
1525)
else
(if i.val < 847 then
1526
else
1527))))
else
(if i.val < 856 then
(if i.val < 852 then
(if i.val < 850 then
(if i.val < 849 then
1528
else
1529)
else
(if i.val < 851 then
1530
else
1531))
else
(if i.val < 854 then
(if i.val < 853 then
1532
else
1533)
else
(if i.val < 855 then
187
else
1534)))
else
(if i.val < 860 then
(if i.val < 858 then
(if i.val < 857 then
1237
else
1535)
else
(if i.val < 859 then
1536
else
1173))
else
(if i.val < 862 then
(if i.val < 861 then
347
else
783)
else
(if i.val < 863 then
1537
else
178)))))
else
(if i.val < 880 then
(if i.val < 872 then
(if i.val < 868 then
(if i.val < 866 then
(if i.val < 865 then
179
else
1538)
else
(if i.val < 867 then
1539
else
1540))
else
(if i.val < 870 then
(if i.val < 869 then
769
else
1541)
else
(if i.val < 871 then
1542
else
1543)))
else
(if i.val < 876 then
(if i.val < 874 then
(if i.val < 873 then
1544
else
228)
else
(if i.val < 875 then
803
else
332))
else
(if i.val < 878 then
(if i.val < 877 then
1137
else
1545)
else
(if i.val < 879 then
1546
else
772))))
else
(if i.val < 888 then
(if i.val < 884 then
(if i.val < 882 then
(if i.val < 881 then
1547
else
1548)
else
(if i.val < 883 then
1549
else
1550))
else
(if i.val < 886 then
(if i.val < 885 then
1551
else
1552)
else
(if i.val < 887 then
932
else
1553)))
else
(if i.val < 892 then
(if i.val < 890 then
(if i.val < 889 then
1554
else
1555)
else
(if i.val < 891 then
1556
else
372))
else
(if i.val < 894 then
(if i.val < 893 then
1238
else
882)
else
(if i.val < 895 then
1557
else
1558)))))))
else
(if i.val < 960 then
(if i.val < 928 then
(if i.val < 912 then
(if i.val < 904 then
(if i.val < 900 then
(if i.val < 898 then
(if i.val < 897 then
1559
else
767)
else
(if i.val < 899 then
1560
else
198))
else
(if i.val < 902 then
(if i.val < 901 then
1803
else
1804)
else
(if i.val < 903 then
1805
else
1806)))
else
(if i.val < 908 then
(if i.val < 906 then
(if i.val < 905 then
2000
else
2001)
else
(if i.val < 907 then
2002
else
2003))
else
(if i.val < 910 then
(if i.val < 909 then
1840
else
2004)
else
(if i.val < 911 then
210
else
2005))))
else
(if i.val < 920 then
(if i.val < 916 then
(if i.val < 914 then
(if i.val < 913 then
339
else
2006)
else
(if i.val < 915 then
2007
else
2008))
else
(if i.val < 918 then
(if i.val < 917 then
1242
else
167)
else
(if i.val < 919 then
1835
else
998)))
else
(if i.val < 924 then
(if i.val < 922 then
(if i.val < 921 then
1836
else
1207)
else
(if i.val < 923 then
377
else
1837))
else
(if i.val < 926 then
(if i.val < 925 then
1838
else
445)
else
(if i.val < 927 then
181
else
1839)))))
else
(if i.val < 944 then
(if i.val < 936 then
(if i.val < 932 then
(if i.val < 930 then
(if i.val < 929 then
1841
else
1842)
else
(if i.val < 931 then
1843
else
2386))
else
(if i.val < 934 then
(if i.val < 933 then
2387
else
2388)
else
(if i.val < 935 then
2389
else
2390)))
else
(if i.val < 940 then
(if i.val < 938 then
(if i.val < 937 then
2391
else
2392)
else
(if i.val < 939 then
2393
else
2394))
else
(if i.val < 942 then
(if i.val < 941 then
2080
else
2395)
else
(if i.val < 943 then
2396
else
2397))))
else
(if i.val < 952 then
(if i.val < 948 then
(if i.val < 946 then
(if i.val < 945 then
2398
else
1131)
else
(if i.val < 947 then
2399
else
523))
else
(if i.val < 950 then
(if i.val < 949 then
1917
else
364)
else
(if i.val < 951 then
2400
else
2401)))
else
(if i.val < 956 then
(if i.val < 954 then
(if i.val < 953 then
2402
else
1739)
else
(if i.val < 955 then
1737
else
2403))
else
(if i.val < 958 then
(if i.val < 957 then
1861
else
2404)
else
(if i.val < 959 then
2405
else
2406))))))
else
(if i.val < 992 then
(if i.val < 976 then
(if i.val < 968 then
(if i.val < 964 then
(if i.val < 962 then
(if i.val < 961 then
2407
else
806)
else
(if i.val < 963 then
1699
else
2408))
else
(if i.val < 966 then
(if i.val < 965 then
1797
else
2409)
else
(if i.val < 967 then
2410
else
2052)))
else
(if i.val < 972 then
(if i.val < 970 then
(if i.val < 969 then
2050
else
1926)
else
(if i.val < 971 then
2411
else
2179))
else
(if i.val < 974 then
(if i.val < 973 then
2412
else
2413)
else
(if i.val < 975 then
2414
else
1275))))
else
(if i.val < 984 then
(if i.val < 980 then
(if i.val < 978 then
(if i.val < 977 then
2415
else
2416)
else
(if i.val < 979 then
2417
else
437))
else
(if i.val < 982 then
(if i.val < 981 then
2418
else
2419)
else
(if i.val < 983 then
2085
else
1135)))
else
(if i.val < 988 then
(if i.val < 986 then
(if i.val < 985 then
1219
else
2262)
else
(if i.val < 987 then
2420
else
514))
else
(if i.val < 990 then
(if i.val < 989 then
2421
else
1903)
else
(if i.val < 991 then
453
else
2422)))))
else
(if i.val < 1008 then
(if i.val < 1000 then
(if i.val < 996 then
(if i.val < 994 then
(if i.val < 993 then
562
else
2423)
else
(if i.val < 995 then
1807
else
2424))
else
(if i.val < 998 then
(if i.val < 997 then
2425
else
2426)
else
(if i.val < 999 then
410
else
2427)))
else
(if i.val < 1004 then
(if i.val < 1002 then
(if i.val < 1001 then
2322
else
976)
else
(if i.val < 1003 then
185
else
1987))
else
(if i.val < 1006 then
(if i.val < 1005 then
2428
else
1979)
else
(if i.val < 1007 then
2429
else
1875))))
else
(if i.val < 1016 then
(if i.val < 1012 then
(if i.val < 1010 then
(if i.val < 1009 then
2430
else
1790)
else
(if i.val < 1011 then
2431
else
2432))
else
(if i.val < 1014 then
(if i.val < 1013 then
2433
else
2434)
else
(if i.val < 1015 then
2435
else
200)))
else
(if i.val < 1020 then
(if i.val < 1018 then
(if i.val < 1017 then
201
else
202)
else
(if i.val < 1019 then
204
else
206))
else
(if i.val < 1022 then
(if i.val < 1021 then
207
else
208)
else
(if i.val < 1023 then
209
else
211)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0002 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1280 then
(if i.val < 1152 then
(if i.val < 1088 then
(if i.val < 1056 then
(if i.val < 1040 then
(if i.val < 1032 then
(if i.val < 1028 then
(if i.val < 1026 then
(if i.val < 1025 then
212
else
215)
else
(if i.val < 1027 then
216
else
217))
else
(if i.val < 1030 then
(if i.val < 1029 then
219
else
2009)
else
(if i.val < 1031 then
2010
else
2011)))
else
(if i.val < 1036 then
(if i.val < 1034 then
(if i.val < 1033 then
2012
else
2013)
else
(if i.val < 1035 then
2014
else
2015))
else
(if i.val < 1038 then
(if i.val < 1037 then
1088
else
2016)
else
(if i.val < 1039 then
1827
else
2017))))
else
(if i.val < 1048 then
(if i.val < 1044 then
(if i.val < 1042 then
(if i.val < 1041 then
1086
else
2018)
else
(if i.val < 1043 then
2019
else
1752))
else
(if i.val < 1046 then
(if i.val < 1045 then
1747
else
2020)
else
(if i.val < 1047 then
987
else
2021)))
else
(if i.val < 1052 then
(if i.val < 1050 then
(if i.val < 1049 then
2022
else
2023)
else
(if i.val < 1051 then
383
else
2024))
else
(if i.val < 1054 then
(if i.val < 1053 then
1750
else
947)
else
(if i.val < 1055 then
2025
else
2026)))))
else
(if i.val < 1072 then
(if i.val < 1064 then
(if i.val < 1060 then
(if i.val < 1058 then
(if i.val < 1057 then
2027
else
169)
else
(if i.val < 1059 then
171
else
1808))
else
(if i.val < 1062 then
(if i.val < 1061 then
1809
else
883)
else
(if i.val < 1063 then
1249
else
1810)))
else
(if i.val < 1068 then
(if i.val < 1066 then
(if i.val < 1065 then
1811
else
1812)
else
(if i.val < 1067 then
1813
else
1814))
else
(if i.val < 1070 then
(if i.val < 1069 then
1815
else
1816)
else
(if i.val < 1071 then
807
else
1817))))
else
(if i.val < 1080 then
(if i.val < 1076 then
(if i.val < 1074 then
(if i.val < 1073 then
459
else
838)
else
(if i.val < 1075 then
1818
else
1819))
else
(if i.val < 1078 then
(if i.val < 1077 then
1820
else
1821)
else
(if i.val < 1079 then
1822
else
1823)))
else
(if i.val < 1084 then
(if i.val < 1082 then
(if i.val < 1081 then
1824
else
1825)
else
(if i.val < 1083 then
1826
else
1828))
else
(if i.val < 1086 then
(if i.val < 1085 then
1829
else
1830)
else
(if i.val < 1087 then
509
else
1831))))))
else
(if i.val < 1120 then
(if i.val < 1104 then
(if i.val < 1096 then
(if i.val < 1092 then
(if i.val < 1090 then
(if i.val < 1089 then
505
else
1832)
else
(if i.val < 1091 then
1833
else
1213))
else
(if i.val < 1094 then
(if i.val < 1093 then
1834
else
824)
else
(if i.val < 1095 then
2028
else
565)))
else
(if i.val < 1100 then
(if i.val < 1098 then
(if i.val < 1097 then
327
else
2029)
else
(if i.val < 1099 then
1107
else
2030))
else
(if i.val < 1102 then
(if i.val < 1101 then
2031
else
2032)
else
(if i.val < 1103 then
2033
else
2034))))
else
(if i.val < 1112 then
(if i.val < 1108 then
(if i.val < 1106 then
(if i.val < 1105 then
591
else
595)
else
(if i.val < 1107 then
588
else
2035))
else
(if i.val < 1110 then
(if i.val < 1109 then
2036
else
2037)
else
(if i.val < 1111 then
2038
else
1089)))
else
(if i.val < 1116 then
(if i.val < 1114 then
(if i.val < 1113 then
2039
else
2040)
else
(if i.val < 1115 then
2041
else
2042))
else
(if i.val < 1118 then
(if i.val < 1117 then
2043
else
2044)
else
(if i.val < 1119 then
2045
else
2046)))))
else
(if i.val < 1136 then
(if i.val < 1128 then
(if i.val < 1124 then
(if i.val < 1122 then
(if i.val < 1121 then
2047
else
2048)
else
(if i.val < 1123 then
2049
else
2051))
else
(if i.val < 1126 then
(if i.val < 1125 then
1946
else
1856)
else
(if i.val < 1127 then
1094
else
2053)))
else
(if i.val < 1132 then
(if i.val < 1130 then
(if i.val < 1129 then
2054
else
2055)
else
(if i.val < 1131 then
2056
else
2057))
else
(if i.val < 1134 then
(if i.val < 1133 then
2058
else
397)
else
(if i.val < 1135 then
2059
else
2060))))
else
(if i.val < 1144 then
(if i.val < 1140 then
(if i.val < 1138 then
(if i.val < 1137 then
175
else
2061)
else
(if i.val < 1139 then
1693
else
398))
else
(if i.val < 1142 then
(if i.val < 1141 then
342
else
2062)
else
(if i.val < 1143 then
2063
else
2064)))
else
(if i.val < 1148 then
(if i.val < 1146 then
(if i.val < 1145 then
2065
else
2066)
else
(if i.val < 1147 then
2067
else
2068))
else
(if i.val < 1150 then
(if i.val < 1149 then
2436
else
2437)
else
(if i.val < 1151 then
802
else
830)))))))
else
(if i.val < 1216 then
(if i.val < 1184 then
(if i.val < 1168 then
(if i.val < 1160 then
(if i.val < 1156 then
(if i.val < 1154 then
(if i.val < 1153 then
834
else
335)
else
(if i.val < 1155 then
827
else
2438))
else
(if i.val < 1158 then
(if i.val < 1157 then
2439
else
2440)
else
(if i.val < 1159 then
2441
else
2442)))
else
(if i.val < 1164 then
(if i.val < 1162 then
(if i.val < 1161 then
2443
else
2444)
else
(if i.val < 1163 then
897
else
2445))
else
(if i.val < 1166 then
(if i.val < 1165 then
2446
else
2447)
else
(if i.val < 1167 then
898
else
884))))
else
(if i.val < 1176 then
(if i.val < 1172 then
(if i.val < 1170 then
(if i.val < 1169 then
885
else
2448)
else
(if i.val < 1171 then
2083
else
2449))
else
(if i.val < 1174 then
(if i.val < 1173 then
2450
else
2451)
else
(if i.val < 1175 then
2452
else
2453)))
else
(if i.val < 1180 then
(if i.val < 1178 then
(if i.val < 1177 then
2454
else
2455)
else
(if i.val < 1179 then
2456
else
1794))
else
(if i.val < 1182 then
(if i.val < 1181 then
2457
else
2458)
else
(if i.val < 1183 then
2459
else
2460)))))
else
(if i.val < 1200 then
(if i.val < 1192 then
(if i.val < 1188 then
(if i.val < 1186 then
(if i.val < 1185 then
2461
else
2462)
else
(if i.val < 1187 then
2463
else
2464))
else
(if i.val < 1190 then
(if i.val < 1189 then
2465
else
2466)
else
(if i.val < 1191 then
2467
else
2468)))
else
(if i.val < 1196 then
(if i.val < 1194 then
(if i.val < 1193 then
2469
else
357)
else
(if i.val < 1195 then
1664
else
1102))
else
(if i.val < 1198 then
(if i.val < 1197 then
1278
else
2470)
else
(if i.val < 1199 then
231
else
2471))))
else
(if i.val < 1208 then
(if i.val < 1204 then
(if i.val < 1202 then
(if i.val < 1201 then
2472
else
2473)
else
(if i.val < 1203 then
2474
else
2475))
else
(if i.val < 1206 then
(if i.val < 1205 then
2476
else
2477)
else
(if i.val < 1207 then
2478
else
413)))
else
(if i.val < 1212 then
(if i.val < 1210 then
(if i.val < 1209 then
2479
else
2480)
else
(if i.val < 1211 then
2481
else
2291))
else
(if i.val < 1214 then
(if i.val < 1213 then
2145
else
2482)
else
(if i.val < 1215 then
2483
else
2484))))))
else
(if i.val < 1248 then
(if i.val < 1232 then
(if i.val < 1224 then
(if i.val < 1220 then
(if i.val < 1218 then
(if i.val < 1217 then
2485
else
2486)
else
(if i.val < 1219 then
2487
else
2488))
else
(if i.val < 1222 then
(if i.val < 1221 then
2489
else
1956)
else
(if i.val < 1223 then
2490
else
1590)))
else
(if i.val < 1228 then
(if i.val < 1226 then
(if i.val < 1225 then
379
else
2491)
else
(if i.val < 1227 then
2492
else
2493))
else
(if i.val < 1230 then
(if i.val < 1229 then
837
else
2494)
else
(if i.val < 1231 then
2495
else
2496))))
else
(if i.val < 1240 then
(if i.val < 1236 then
(if i.val < 1234 then
(if i.val < 1233 then
2497
else
2498)
else
(if i.val < 1235 then
2499
else
2500))
else
(if i.val < 1238 then
(if i.val < 1237 then
1959
else
2501)
else
(if i.val < 1239 then
2502
else
2503)))
else
(if i.val < 1244 then
(if i.val < 1242 then
(if i.val < 1241 then
425
else
1915)
else
(if i.val < 1243 then
496
else
2504))
else
(if i.val < 1246 then
(if i.val < 1245 then
2505
else
2506)
else
(if i.val < 1247 then
2507
else
2508)))))
else
(if i.val < 1264 then
(if i.val < 1256 then
(if i.val < 1252 then
(if i.val < 1250 then
(if i.val < 1249 then
417
else
418)
else
(if i.val < 1251 then
1593
else
1662))
else
(if i.val < 1254 then
(if i.val < 1253 then
2509
else
2510)
else
(if i.val < 1255 then
2511
else
2512)))
else
(if i.val < 1260 then
(if i.val < 1258 then
(if i.val < 1257 then
2513
else
2514)
else
(if i.val < 1259 then
1857
else
2515))
else
(if i.val < 1262 then
(if i.val < 1261 then
2516
else
2517)
else
(if i.val < 1263 then
2518
else
1997))))
else
(if i.val < 1272 then
(if i.val < 1268 then
(if i.val < 1266 then
(if i.val < 1265 then
189
else
2519)
else
(if i.val < 1267 then
2520
else
2521))
else
(if i.val < 1270 then
(if i.val < 1269 then
2122
else
1212)
else
(if i.val < 1271 then
1845
else
2522)))
else
(if i.val < 1276 then
(if i.val < 1274 then
(if i.val < 1273 then
2523
else
1938)
else
(if i.val < 1275 then
593
else
2244))
else
(if i.val < 1278 then
(if i.val < 1277 then
2384
else
2524)
else
(if i.val < 1279 then
2243
else
2525))))))))
else
(if i.val < 1408 then
(if i.val < 1344 then
(if i.val < 1312 then
(if i.val < 1296 then
(if i.val < 1288 then
(if i.val < 1284 then
(if i.val < 1282 then
(if i.val < 1281 then
2135
else
2526)
else
(if i.val < 1283 then
1896
else
1722))
else
(if i.val < 1286 then
(if i.val < 1285 then
2069
else
1248)
else
(if i.val < 1287 then
2070
else
2071)))
else
(if i.val < 1292 then
(if i.val < 1290 then
(if i.val < 1289 then
385
else
1676)
else
(if i.val < 1291 then
1240
else
2527))
else
(if i.val < 1294 then
(if i.val < 1293 then
1596
else
1595)
else
(if i.val < 1295 then
2528
else
2529))))
else
(if i.val < 1304 then
(if i.val < 1300 then
(if i.val < 1298 then
(if i.val < 1297 then
2334
else
2530)
else
(if i.val < 1299 then
1679
else
1655))
else
(if i.val < 1302 then
(if i.val < 1301 then
979
else
2531)
else
(if i.val < 1303 then
2532
else
2533)))
else
(if i.val < 1308 then
(if i.val < 1306 then
(if i.val < 1305 then
1851
else
2363)
else
(if i.val < 1307 then
2534
else
925))
else
(if i.val < 1310 then
(if i.val < 1309 then
2535
else
2536)
else
(if i.val < 1311 then
1733
else
1984)))))
else
(if i.val < 1328 then
(if i.val < 1320 then
(if i.val < 1316 then
(if i.val < 1314 then
(if i.val < 1313 then
990
else
1732)
else
(if i.val < 1315 then
1734
else
2345))
else
(if i.val < 1318 then
(if i.val < 1317 then
2364
else
1072)
else
(if i.val < 1319 then
2094
else
2537)))
else
(if i.val < 1324 then
(if i.val < 1322 then
(if i.val < 1321 then
1762
else
2335)
else
(if i.val < 1323 then
2538
else
1774))
else
(if i.val < 1326 then
(if i.val < 1325 then
2539
else
1710)
else
(if i.val < 1327 then
2123
else
791))))
else
(if i.val < 1336 then
(if i.val < 1332 then
(if i.val < 1330 then
(if i.val < 1329 then
815
else
2540)
else
(if i.val < 1331 then
362
else
358))
else
(if i.val < 1334 then
(if i.val < 1333 then
1723
else
2541)
else
(if i.val < 1335 then
1948
else
842)))
else
(if i.val < 1340 then
(if i.val < 1338 then
(if i.val < 1337 then
2542
else
2543)
else
(if i.val < 1339 then
2544
else
2545))
else
(if i.val < 1342 then
(if i.val < 1341 then
2166
else
2546)
else
(if i.val < 1343 then
2547
else
2548))))))
else
(if i.val < 1376 then
(if i.val < 1360 then
(if i.val < 1352 then
(if i.val < 1348 then
(if i.val < 1346 then
(if i.val < 1345 then
810
else
2549)
else
(if i.val < 1347 then
992
else
1889))
else
(if i.val < 1350 then
(if i.val < 1349 then
2550
else
1095)
else
(if i.val < 1351 then
443
else
2551)))
else
(if i.val < 1356 then
(if i.val < 1354 then
(if i.val < 1353 then
2552
else
2553)
else
(if i.val < 1355 then
2554
else
2555))
else
(if i.val < 1358 then
(if i.val < 1357 then
1796
else
2187)
else
(if i.val < 1359 then
2556
else
2557))))
else
(if i.val < 1368 then
(if i.val < 1364 then
(if i.val < 1362 then
(if i.val < 1361 then
2087
else
2558)
else
(if i.val < 1363 then
2559
else
2560))
else
(if i.val < 1366 then
(if i.val < 1365 then
2561
else
2562)
else
(if i.val < 1367 then
1106
else
2563)))
else
(if i.val < 1372 then
(if i.val < 1370 then
(if i.val < 1369 then
2564
else
1104)
else
(if i.val < 1371 then
2565
else
1274))
else
(if i.val < 1374 then
(if i.val < 1373 then
2121
else
1105)
else
(if i.val < 1375 then
176
else
177)))))
else
(if i.val < 1392 then
(if i.val < 1384 then
(if i.val < 1380 then
(if i.val < 1378 then
(if i.val < 1377 then
180
else
182)
else
(if i.val < 1379 then
186
else
220))
else
(if i.val < 1382 then
(if i.val < 1381 then
221
else
222)
else
(if i.val < 1383 then
223
else
224)))
else
(if i.val < 1388 then
(if i.val < 1386 then
(if i.val < 1385 then
226
else
229)
else
(if i.val < 1387 then
232
else
233))
else
(if i.val < 1390 then
(if i.val < 1389 then
234
else
235)
else
(if i.val < 1391 then
236
else
237))))
else
(if i.val < 1400 then
(if i.val < 1396 then
(if i.val < 1394 then
(if i.val < 1393 then
238
else
239)
else
(if i.val < 1395 then
240
else
243))
else
(if i.val < 1398 then
(if i.val < 1397 then
244
else
245)
else
(if i.val < 1399 then
246
else
247)))
else
(if i.val < 1404 then
(if i.val < 1402 then
(if i.val < 1401 then
248
else
249)
else
(if i.val < 1403 then
250
else
252))
else
(if i.val < 1406 then
(if i.val < 1405 then
253
else
328)
else
(if i.val < 1407 then
329
else
330)))))))
else
(if i.val < 1472 then
(if i.val < 1440 then
(if i.val < 1424 then
(if i.val < 1416 then
(if i.val < 1412 then
(if i.val < 1410 then
(if i.val < 1409 then
331
else
333)
else
(if i.val < 1411 then
334
else
336))
else
(if i.val < 1414 then
(if i.val < 1413 then
337
else
338)
else
(if i.val < 1415 then
340
else
341)))
else
(if i.val < 1420 then
(if i.val < 1418 then
(if i.val < 1417 then
344
else
345)
else
(if i.val < 1419 then
346
else
349))
else
(if i.val < 1422 then
(if i.val < 1421 then
350
else
351)
else
(if i.val < 1423 then
352
else
353))))
else
(if i.val < 1432 then
(if i.val < 1428 then
(if i.val < 1426 then
(if i.val < 1425 then
355
else
356)
else
(if i.val < 1427 then
359
else
360))
else
(if i.val < 1430 then
(if i.val < 1429 then
361
else
363)
else
(if i.val < 1431 then
366
else
368)))
else
(if i.val < 1436 then
(if i.val < 1434 then
(if i.val < 1433 then
370
else
371)
else
(if i.val < 1435 then
373
else
374))
else
(if i.val < 1438 then
(if i.val < 1437 then
375
else
376)
else
(if i.val < 1439 then
378
else
380)))))
else
(if i.val < 1456 then
(if i.val < 1448 then
(if i.val < 1444 then
(if i.val < 1442 then
(if i.val < 1441 then
386
else
387)
else
(if i.val < 1443 then
388
else
389))
else
(if i.val < 1446 then
(if i.val < 1445 then
390
else
391)
else
(if i.val < 1447 then
393
else
394)))
else
(if i.val < 1452 then
(if i.val < 1450 then
(if i.val < 1449 then
396
else
2566)
else
(if i.val < 1451 then
2567
else
1972))
else
(if i.val < 1454 then
(if i.val < 1453 then
2568
else
2569)
else
(if i.val < 1455 then
2570
else
2571))))
else
(if i.val < 1464 then
(if i.val < 1460 then
(if i.val < 1458 then
(if i.val < 1457 then
2572
else
1760)
else
(if i.val < 1459 then
2573
else
2574))
else
(if i.val < 1462 then
(if i.val < 1461 then
2575
else
1764)
else
(if i.val < 1463 then
2576
else
2577)))
else
(if i.val < 1468 then
(if i.val < 1466 then
(if i.val < 1465 then
2578
else
2579)
else
(if i.val < 1467 then
868
else
1965))
else
(if i.val < 1470 then
(if i.val < 1469 then
585
else
879)
else
(if i.val < 1471 then
2580
else
2581))))))
else
(if i.val < 1504 then
(if i.val < 1488 then
(if i.val < 1480 then
(if i.val < 1476 then
(if i.val < 1474 then
(if i.val < 1473 then
2582
else
2583)
else
(if i.val < 1475 then
2584
else
1671))
else
(if i.val < 1478 then
(if i.val < 1477 then
2257
else
2585)
else
(if i.val < 1479 then
861
else
2213)))
else
(if i.val < 1484 then
(if i.val < 1482 then
(if i.val < 1481 then
1669
else
820)
else
(if i.val < 1483 then
2586
else
1712))
else
(if i.val < 1486 then
(if i.val < 1485 then
1773
else
2587)
else
(if i.val < 1487 then
1743
else
1763))))
else
(if i.val < 1496 then
(if i.val < 1492 then
(if i.val < 1490 then
(if i.val < 1489 then
2588
else
1643)
else
(if i.val < 1491 then
2589
else
2590))
else
(if i.val < 1494 then
(if i.val < 1493 then
2591
else
2592)
else
(if i.val < 1495 then
1150
else
874)))
else
(if i.val < 1500 then
(if i.val < 1498 then
(if i.val < 1497 then
1610
else
2593)
else
(if i.val < 1499 then
961
else
1070))
else
(if i.val < 1502 then
(if i.val < 1501 then
2594
else
2595)
else
(if i.val < 1503 then
2347
else
2210)))))
else
(if i.val < 1520 then
(if i.val < 1512 then
(if i.val < 1508 then
(if i.val < 1506 then
(if i.val < 1505 then
2205
else
2596)
else
(if i.val < 1507 then
2597
else
2110))
else
(if i.val < 1510 then
(if i.val < 1509 then
1093
else
1916)
else
(if i.val < 1511 then
521
else
1154)))
else
(if i.val < 1516 then
(if i.val < 1514 then
(if i.val < 1513 then
2598
else
1151)
else
(if i.val < 1515 then
2599
else
1694))
else
(if i.val < 1518 then
(if i.val < 1517 then
1152
else
2600)
else
(if i.val < 1519 then
2184
else
1228))))
else
(if i.val < 1528 then
(if i.val < 1524 then
(if i.val < 1522 then
(if i.val < 1521 then
1073
else
1675)
else
(if i.val < 1523 then
2193
else
777))
else
(if i.val < 1526 then
(if i.val < 1525 then
2601
else
2602)
else
(if i.val < 1527 then
2603
else
1787)))
else
(if i.val < 1532 then
(if i.val < 1530 then
(if i.val < 1529 then
2604
else
2605)
else
(if i.val < 1531 then
2606
else
2607))
else
(if i.val < 1534 then
(if i.val < 1533 then
2608
else
2609)
else
(if i.val < 1535 then
2610
else
426)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0003 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 1792 then
(if i.val < 1664 then
(if i.val < 1600 then
(if i.val < 1568 then
(if i.val < 1552 then
(if i.val < 1544 then
(if i.val < 1540 then
(if i.val < 1538 then
(if i.val < 1537 then
2611
else
2612)
else
(if i.val < 1539 then
808
else
1801))
else
(if i.val < 1542 then
(if i.val < 1541 then
2613
else
1630)
else
(if i.val < 1543 then
2614
else
2615)))
else
(if i.val < 1548 then
(if i.val < 1546 then
(if i.val < 1545 then
2616
else
2617)
else
(if i.val < 1547 then
1674
else
2618))
else
(if i.val < 1550 then
(if i.val < 1549 then
1793
else
893)
else
(if i.val < 1551 then
1061
else
1167))))
else
(if i.val < 1560 then
(if i.val < 1556 then
(if i.val < 1554 then
(if i.val < 1553 then
1168
else
2619)
else
(if i.val < 1555 then
2620
else
2621))
else
(if i.val < 1558 then
(if i.val < 1557 then
2194
else
2622)
else
(if i.val < 1559 then
1600
else
1578)))
else
(if i.val < 1564 then
(if i.val < 1562 then
(if i.val < 1561 then
1166
else
1910)
else
(if i.val < 1563 then
2623
else
973))
else
(if i.val < 1566 then
(if i.val < 1565 then
2327
else
2624)
else
(if i.val < 1567 then
2344
else
2326)))))
else
(if i.val < 1584 then
(if i.val < 1576 then
(if i.val < 1572 then
(if i.val < 1570 then
(if i.val < 1569 then
2625
else
2321)
else
(if i.val < 1571 then
2325
else
2266))
else
(if i.val < 1574 then
(if i.val < 1573 then
2234
else
2626)
else
(if i.val < 1575 then
2331
else
1592)))
else
(if i.val < 1580 then
(if i.val < 1578 then
(if i.val < 1577 then
2134
else
2627)
else
(if i.val < 1579 then
896
else
2628))
else
(if i.val < 1582 then
(if i.val < 1581 then
2629
else
2630)
else
(if i.val < 1583 then
1761
else
2308))))
else
(if i.val < 1592 then
(if i.val < 1588 then
(if i.val < 1586 then
(if i.val < 1585 then
2631
else
2275)
else
(if i.val < 1587 then
2313
else
2632))
else
(if i.val < 1590 then
(if i.val < 1589 then
2633
else
2634)
else
(if i.val < 1591 then
1906
else
2635)))
else
(if i.val < 1596 then
(if i.val < 1594 then
(if i.val < 1593 then
2636
else
2637)
else
(if i.val < 1595 then
2638
else
429))
else
(if i.val < 1598 then
(if i.val < 1597 then
428
else
2639)
else
(if i.val < 1599 then
2640
else
2309))))))
else
(if i.val < 1632 then
(if i.val < 1616 then
(if i.val < 1608 then
(if i.val < 1604 then
(if i.val < 1602 then
(if i.val < 1601 then
895
else
2641)
else
(if i.val < 1603 then
1672
else
1188))
else
(if i.val < 1606 then
(if i.val < 1605 then
2642
else
2643)
else
(if i.val < 1607 then
2644
else
2645)))
else
(if i.val < 1612 then
(if i.val < 1610 then
(if i.val < 1609 then
2646
else
1713)
else
(if i.val < 1611 then
804
else
2330))
else
(if i.val < 1614 then
(if i.val < 1613 then
2647
else
2648)
else
(if i.val < 1615 then
2649
else
2650))))
else
(if i.val < 1624 then
(if i.val < 1620 then
(if i.val < 1618 then
(if i.val < 1617 then
2651
else
2652)
else
(if i.val < 1619 then
1729
else
1993))
else
(if i.val < 1622 then
(if i.val < 1621 then
2653
else
2654)
else
(if i.val < 1623 then
1083
else
2655)))
else
(if i.val < 1628 then
(if i.val < 1626 then
(if i.val < 1625 then
2656
else
1780)
else
(if i.val < 1627 then
2279
else
2657))
else
(if i.val < 1630 then
(if i.val < 1629 then
2658
else
2659)
else
(if i.val < 1631 then
869
else
2660)))))
else
(if i.val < 1648 then
(if i.val < 1640 then
(if i.val < 1636 then
(if i.val < 1634 then
(if i.val < 1633 then
1695
else
2661)
else
(if i.val < 1635 then
2160
else
2162))
else
(if i.val < 1638 then
(if i.val < 1637 then
2253
else
966)
else
(if i.val < 1639 then
1879
else
2662)))
else
(if i.val < 1644 then
(if i.val < 1642 then
(if i.val < 1641 then
1924
else
943)
else
(if i.val < 1643 then
1922
else
796))
else
(if i.val < 1646 then
(if i.val < 1645 then
2663
else
2664)
else
(if i.val < 1647 then
1688
else
2665))))
else
(if i.val < 1656 then
(if i.val < 1652 then
(if i.val < 1650 then
(if i.val < 1649 then
1063
else
2666)
else
(if i.val < 1651 then
2667
else
2668))
else
(if i.val < 1654 then
(if i.val < 1653 then
1735
else
2669)
else
(if i.val < 1655 then
2250
else
435)))
else
(if i.val < 1660 then
(if i.val < 1658 then
(if i.val < 1657 then
2261
else
2670)
else
(if i.val < 1659 then
1657
else
2671))
else
(if i.val < 1662 then
(if i.val < 1661 then
2672
else
2673)
else
(if i.val < 1663 then
2674
else
1066)))))))
else
(if i.val < 1728 then
(if i.val < 1696 then
(if i.val < 1680 then
(if i.val < 1672 then
(if i.val < 1668 then
(if i.val < 1666 then
(if i.val < 1665 then
2675
else
2676)
else
(if i.val < 1667 then
2677
else
2678))
else
(if i.val < 1670 then
(if i.val < 1669 then
2679
else
785)
else
(if i.val < 1671 then
2680
else
780)))
else
(if i.val < 1676 then
(if i.val < 1674 then
(if i.val < 1673 then
1749
else
2681)
else
(if i.val < 1675 then
878
else
839))
else
(if i.val < 1678 then
(if i.val < 1677 then
424
else
2682)
else
(if i.val < 1679 then
2683
else
434))))
else
(if i.val < 1688 then
(if i.val < 1684 then
(if i.val < 1682 then
(if i.val < 1681 then
1627
else
1192)
else
(if i.val < 1683 then
1772
else
2684))
else
(if i.val < 1686 then
(if i.val < 1685 then
2685
else
1748)
else
(if i.val < 1687 then
2337
else
2686)))
else
(if i.val < 1692 then
(if i.val < 1690 then
(if i.val < 1689 then
2258
else
2687)
else
(if i.val < 1691 then
2688
else
2371))
else
(if i.val < 1694 then
(if i.val < 1693 then
2689
else
2690)
else
(if i.val < 1695 then
833
else
2691)))))
else
(if i.val < 1712 then
(if i.val < 1704 then
(if i.val < 1700 then
(if i.val < 1698 then
(if i.val < 1697 then
2692
else
2693)
else
(if i.val < 1699 then
2694
else
2695))
else
(if i.val < 1702 then
(if i.val < 1701 then
2696
else
2697)
else
(if i.val < 1703 then
2698
else
2699)))
else
(if i.val < 1708 then
(if i.val < 1706 then
(if i.val < 1705 then
2700
else
1656)
else
(if i.val < 1707 then
2701
else
2702))
else
(if i.val < 1710 then
(if i.val < 1709 then
2703
else
2195)
else
(if i.val < 1711 then
539
else
1620))))
else
(if i.val < 1720 then
(if i.val < 1716 then
(if i.val < 1714 then
(if i.val < 1713 then
788
else
2238)
else
(if i.val < 1715 then
2704
else
2705))
else
(if i.val < 1718 then
(if i.val < 1717 then
2706
else
2315)
else
(if i.val < 1719 then
2707
else
2708)))
else
(if i.val < 1724 then
(if i.val < 1722 then
(if i.val < 1721 then
2709
else
1858)
else
(if i.val < 1723 then
415
else
546))
else
(if i.val < 1726 then
(if i.val < 1725 then
2710
else
2711)
else
(if i.val < 1727 then
2712
else
2713))))))
else
(if i.val < 1760 then
(if i.val < 1744 then
(if i.val < 1736 then
(if i.val < 1732 then
(if i.val < 1730 then
(if i.val < 1729 then
2714
else
2715)
else
(if i.val < 1731 then
2716
else
2717))
else
(if i.val < 1734 then
(if i.val < 1733 then
454
else
450)
else
(if i.val < 1735 then
455
else
1846)))
else
(if i.val < 1740 then
(if i.val < 1738 then
(if i.val < 1737 then
2718
else
1848)
else
(if i.val < 1739 then
1569
else
2719))
else
(if i.val < 1742 then
(if i.val < 1741 then
2720
else
2721)
else
(if i.val < 1743 then
2722
else
792))))
else
(if i.val < 1752 then
(if i.val < 1748 then
(if i.val < 1746 then
(if i.val < 1745 then
2723
else
1132)
else
(if i.val < 1747 then
2724
else
436))
else
(if i.val < 1750 then
(if i.val < 1749 then
2725
else
1602)
else
(if i.val < 1751 then
522
else
1625)))
else
(if i.val < 1756 then
(if i.val < 1754 then
(if i.val < 1753 then
512
else
2726)
else
(if i.val < 1755 then
2727
else
967))
else
(if i.val < 1758 then
(if i.val < 1757 then
2728
else
2305)
else
(if i.val < 1759 then
2729
else
2730)))))
else
(if i.val < 1776 then
(if i.val < 1768 then
(if i.val < 1764 then
(if i.val < 1762 then
(if i.val < 1761 then
758
else
2731)
else
(if i.val < 1763 then
531
else
793))
else
(if i.val < 1766 then
(if i.val < 1765 then
763
else
2732)
else
(if i.val < 1767 then
2733
else
2734)))
else
(if i.val < 1772 then
(if i.val < 1770 then
(if i.val < 1769 then
1591
else
1179)
else
(if i.val < 1771 then
1606
else
2735))
else
(if i.val < 1774 then
(if i.val < 1773 then
2736
else
789)
else
(if i.val < 1775 then
534
else
2252))))
else
(if i.val < 1784 then
(if i.val < 1780 then
(if i.val < 1778 then
(if i.val < 1777 then
2737
else
2738)
else
(if i.val < 1779 then
2739
else
2740))
else
(if i.val < 1782 then
(if i.val < 1781 then
1751
else
2741)
else
(if i.val < 1783 then
1014
else
2742)))
else
(if i.val < 1788 then
(if i.val < 1786 then
(if i.val < 1785 then
1864
else
2192)
else
(if i.val < 1787 then
2743
else
847))
else
(if i.val < 1790 then
(if i.val < 1789 then
2744
else
2307)
else
(if i.val < 1791 then
2745
else
2375))))))))
else
(if i.val < 1920 then
(if i.val < 1856 then
(if i.val < 1824 then
(if i.val < 1808 then
(if i.val < 1800 then
(if i.val < 1796 then
(if i.val < 1794 then
(if i.val < 1793 then
2746
else
881)
else
(if i.val < 1795 then
1769
else
2747))
else
(if i.val < 1798 then
(if i.val < 1797 then
574
else
2748)
else
(if i.val < 1799 then
2749
else
2750)))
else
(if i.val < 1804 then
(if i.val < 1802 then
(if i.val < 1801 then
1114
else
866)
else
(if i.val < 1803 then
2751
else
481))
else
(if i.val < 1806 then
(if i.val < 1805 then
482
else
483)
else
(if i.val < 1807 then
484
else
3014))))
else
(if i.val < 1816 then
(if i.val < 1812 then
(if i.val < 1810 then
(if i.val < 1809 then
3015
else
3016)
else
(if i.val < 1811 then
1648
else
3017))
else
(if i.val < 1814 then
(if i.val < 1813 then
3018
else
1663)
else
(if i.val < 1815 then
1970
else
3198)))
else
(if i.val < 1820 then
(if i.val < 1818 then
(if i.val < 1817 then
3199
else
3200)
else
(if i.val < 1819 then
3201
else
2086))
else
(if i.val < 1822 then
(if i.val < 1821 then
3202
else
3045)
else
(if i.val < 1823 then
2109
else
2084)))))
else
(if i.val < 1840 then
(if i.val < 1832 then
(if i.val < 1828 then
(if i.val < 1826 then
(if i.val < 1825 then
3203
else
2823)
else
(if i.val < 1827 then
3204
else
507))
else
(if i.val < 1830 then
(if i.val < 1829 then
1622
else
1892)
else
(if i.val < 1831 then
3205
else
561)))
else
(if i.val < 1836 then
(if i.val < 1834 then
(if i.val < 1833 then
1111
else
2114)
else
(if i.val < 1835 then
3206
else
409))
else
(if i.val < 1838 then
(if i.val < 1837 then
411
else
2323)
else
(if i.val < 1839 then
3038
else
3039))))
else
(if i.val < 1848 then
(if i.val < 1844 then
(if i.val < 1842 then
(if i.val < 1841 then
489
else
581)
else
(if i.val < 1843 then
2286
else
1968))
else
(if i.val < 1846 then
(if i.val < 1845 then
3040
else
2329)
else
(if i.val < 1847 then
1652
else
3041)))
else
(if i.val < 1852 then
(if i.val < 1850 then
(if i.val < 1849 then
954
else
972)
else
(if i.val < 1851 then
3042
else
441))
else
(if i.val < 1854 then
(if i.val < 1853 then
1736
else
3043)
else
(if i.val < 1855 then
3044
else
3046))))))
else
(if i.val < 1888 then
(if i.val < 1872 then
(if i.val < 1864 then
(if i.val < 1860 then
(if i.val < 1858 then
(if i.val < 1857 then
3047
else
3048)
else
(if i.val < 1859 then
3049
else
3050))
else
(if i.val < 1862 then
(if i.val < 1861 then
3051
else
3569)
else
(if i.val < 1863 then
3570
else
3026)))
else
(if i.val < 1868 then
(if i.val < 1866 then
(if i.val < 1865 then
3571
else
3394)
else
(if i.val < 1867 then
2971
else
3572))
else
(if i.val < 1870 then
(if i.val < 1869 then
3573
else
3322)
else
(if i.val < 1871 then
3367
else
3574))))
else
(if i.val < 1880 then
(if i.val < 1876 then
(if i.val < 1874 then
(if i.val < 1873 then
3575
else
3288)
else
(if i.val < 1875 then
3576
else
2939))
else
(if i.val < 1878 then
(if i.val < 1877 then
3577
else
3283)
else
(if i.val < 1879 then
3281
else
3245)))
else
(if i.val < 1884 then
(if i.val < 1882 then
(if i.val < 1881 then
3578
else
1908)
else
(if i.val < 1883 then
3579
else
3468))
else
(if i.val < 1886 then
(if i.val < 1885 then
1966
else
1990)
else
(if i.val < 1887 then
3084
else
3580)))))
else
(if i.val < 1904 then
(if i.val < 1896 then
(if i.val < 1892 then
(if i.val < 1890 then
(if i.val < 1889 then
2115
else
563)
else
(if i.val < 1891 then
3363
else
3581))
else
(if i.val < 1894 then
(if i.val < 1893 then
1084
else
1673)
else
(if i.val < 1895 then
2966
else
1127)))
else
(if i.val < 1900 then
(if i.val < 1898 then
(if i.val < 1897 then
414
else
3582)
else
(if i.val < 1899 then
1781
else
3583))
else
(if i.val < 1902 then
(if i.val < 1901 then
1730
else
3584)
else
(if i.val < 1903 then
3585
else
2937))))
else
(if i.val < 1912 then
(if i.val < 1908 then
(if i.val < 1906 then
(if i.val < 1905 then
2942
else
3074)
else
(if i.val < 1907 then
1223
else
1687))
else
(if i.val < 1910 then
(if i.val < 1909 then
3531
else
2911)
else
(if i.val < 1911 then
3586
else
3114)))
else
(if i.val < 1916 then
(if i.val < 1914 then
(if i.val < 1913 then
3587
else
3588)
else
(if i.val < 1915 then
2254
else
3007))
else
(if i.val < 1918 then
(if i.val < 1917 then
825
else
3275)
else
(if i.val < 1919 then
3372
else
3589)))))))
else
(if i.val < 1984 then
(if i.val < 1952 then
(if i.val < 1936 then
(if i.val < 1928 then
(if i.val < 1924 then
(if i.val < 1922 then
(if i.val < 1921 then
3590
else
3253)
else
(if i.val < 1923 then
3252
else
3137))
else
(if i.val < 1926 then
(if i.val < 1925 then
3260
else
3256)
else
(if i.val < 1927 then
2956
else
3135)))
else
(if i.val < 1932 then
(if i.val < 1930 then
(if i.val < 1929 then
1974
else
1615)
else
(if i.val < 1931 then
988
else
3387))
else
(if i.val < 1934 then
(if i.val < 1933 then
3591
else
3592)
else
(if i.val < 1935 then
2328
else
2926))))
else
(if i.val < 1944 then
(if i.val < 1940 then
(if i.val < 1938 then
(if i.val < 1937 then
3347
else
3227)
else
(if i.val < 1939 then
2385
else
978))
else
(if i.val < 1942 then
(if i.val < 1941 then
3139
else
1923)
else
(if i.val < 1943 then
3593
else
1940)))
else
(if i.val < 1948 then
(if i.val < 1946 then
(if i.val < 1945 then
3594
else
3595)
else
(if i.val < 1947 then
3215
else
3596))
else
(if i.val < 1950 then
(if i.val < 1949 then
548
else
3597)
else
(if i.val < 1951 then
2769
else
3598)))))
else
(if i.val < 1968 then
(if i.val < 1960 then
(if i.val < 1956 then
(if i.val < 1954 then
(if i.val < 1953 then
3318
else
1128)
else
(if i.val < 1955 then
3093
else
3599))
else
(if i.val < 1958 then
(if i.val < 1957 then
2129
else
1118)
else
(if i.val < 1959 then
1741
else
1985)))
else
(if i.val < 1964 then
(if i.val < 1962 then
(if i.val < 1961 then
1577
else
996)
else
(if i.val < 1963 then
1718
else
3600))
else
(if i.val < 1966 then
(if i.val < 1965 then
3192
else
770)
else
(if i.val < 1967 then
3129
else
3233))))
else
(if i.val < 1976 then
(if i.val < 1972 then
(if i.val < 1970 then
(if i.val < 1969 then
930
else
3070)
else
(if i.val < 1971 then
1067
else
3601))
else
(if i.val < 1974 then
(if i.val < 1973 then
751
else
980)
else
(if i.val < 1975 then
3188
else
3602)))
else
(if i.val < 1980 then
(if i.val < 1978 then
(if i.val < 1977 then
3105
else
3103)
else
(if i.val < 1979 then
3161
else
2935))
else
(if i.val < 1982 then
(if i.val < 1981 then
1564
else
3473)
else
(if i.val < 1983 then
3163
else
3329))))))
else
(if i.val < 2016 then
(if i.val < 2000 then
(if i.val < 1992 then
(if i.val < 1988 then
(if i.val < 1986 then
(if i.val < 1985 then
451
else
1236)
else
(if i.val < 1987 then
3183
else
3184))
else
(if i.val < 1990 then
(if i.val < 1989 then
3603
else
1991)
else
(if i.val < 1991 then
3604
else
2817)))
else
(if i.val < 1996 then
(if i.val < 1994 then
(if i.val < 1993 then
3292
else
3605)
else
(if i.val < 1995 then
3002
else
3606))
else
(if i.val < 1998 then
(if i.val < 1997 then
1122
else
3607)
else
(if i.val < 1999 then
3608
else
3609))))
else
(if i.val < 2008 then
(if i.val < 2004 then
(if i.val < 2002 then
(if i.val < 2001 then
485
else
486)
else
(if i.val < 2003 then
487
else
488))
else
(if i.val < 2006 then
(if i.val < 2005 then
490
else
491)
else
(if i.val < 2007 then
493
else
494)))
else
(if i.val < 2012 then
(if i.val < 2010 then
(if i.val < 2009 then
495
else
497)
else
(if i.val < 2011 then
498
else
499))
else
(if i.val < 2014 then
(if i.val < 2013 then
500
else
501)
else
(if i.val < 2015 then
503
else
504)))))
else
(if i.val < 2032 then
(if i.val < 2024 then
(if i.val < 2020 then
(if i.val < 2018 then
(if i.val < 2017 then
506
else
508)
else
(if i.val < 2019 then
510
else
511))
else
(if i.val < 2022 then
(if i.val < 2021 then
513
else
515)
else
(if i.val < 2023 then
517
else
518)))
else
(if i.val < 2028 then
(if i.val < 2026 then
(if i.val < 2025 then
520
else
524)
else
(if i.val < 2027 then
525
else
526))
else
(if i.val < 2030 then
(if i.val < 2029 then
1126
else
3207)
else
(if i.val < 2031 then
3208
else
3209))))
else
(if i.val < 2040 then
(if i.val < 2036 then
(if i.val < 2034 then
(if i.val < 2033 then
3210
else
1195)
else
(if i.val < 2035 then
2156
else
1098))
else
(if i.val < 2038 then
(if i.val < 2037 then
2946
else
3211)
else
(if i.val < 2039 then
2108
else
2117)))
else
(if i.val < 2044 then
(if i.val < 2042 then
(if i.val < 2041 then
3034
else
1800)
else
(if i.val < 2043 then
795
else
2838))
else
(if i.val < 2046 then
(if i.val < 2045 then
3086
else
1957)
else
(if i.val < 2047 then
2116
else
3212)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0004 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2304 then
(if i.val < 2176 then
(if i.val < 2112 then
(if i.val < 2080 then
(if i.val < 2064 then
(if i.val < 2056 then
(if i.val < 2052 then
(if i.val < 2050 then
(if i.val < 2049 then
3213
else
1996)
else
(if i.val < 2051 then
2955
else
3214))
else
(if i.val < 2054 then
(if i.val < 2053 then
1755
else
1895)
else
(if i.val < 2055 then
1953
else
3138)))
else
(if i.val < 2060 then
(if i.val < 2058 then
(if i.val < 2057 then
3216
else
945)
else
(if i.val < 2059 then
1745
else
3217))
else
(if i.val < 2062 then
(if i.val < 2061 then
983
else
876)
else
(if i.val < 2063 then
2380
else
3218))))
else
(if i.val < 2072 then
(if i.val < 2068 then
(if i.val < 2066 then
(if i.val < 2065 then
3219
else
3220)
else
(if i.val < 2067 then
3221
else
2143))
else
(if i.val < 2070 then
(if i.val < 2069 then
3222
else
416)
else
(if i.val < 2071 then
419
else
420)))
else
(if i.val < 2076 then
(if i.val < 2074 then
(if i.val < 2073 then
1631
else
3019)
else
(if i.val < 2075 then
3020
else
3021))
else
(if i.val < 2078 then
(if i.val < 2077 then
1855
else
1778)
else
(if i.val < 2079 then
2827
else
2348)))))
else
(if i.val < 2096 then
(if i.val < 2088 then
(if i.val < 2084 then
(if i.val < 2082 then
(if i.val < 2081 then
2343
else
3022)
else
(if i.val < 2083 then
3023
else
3024))
else
(if i.val < 2086 then
(if i.val < 2085 then
1079
else
2940)
else
(if i.val < 2087 then
1075
else
579)))
else
(if i.val < 2092 then
(if i.val < 2090 then
(if i.val < 2089 then
1660
else
2178)
else
(if i.val < 2091 then
2346
else
3025))
else
(if i.val < 2094 then
(if i.val < 2093 then
1586
else
986)
else
(if i.val < 2095 then
527
else
1653))))
else
(if i.val < 2104 then
(if i.val < 2100 then
(if i.val < 2098 then
(if i.val < 2097 then
1874
else
3027)
else
(if i.val < 2099 then
1011
else
1008))
else
(if i.val < 2102 then
(if i.val < 2101 then
1704
else
3028)
else
(if i.val < 2103 then
1706
else
3029)))
else
(if i.val < 2108 then
(if i.val < 2106 then
(if i.val < 2105 then
3030
else
3031)
else
(if i.val < 2107 then
3032
else
3033))
else
(if i.val < 2110 then
(if i.val < 2109 then
1110
else
1078)
else
(if i.val < 2111 then
823
else
1707))))))
else
(if i.val < 2144 then
(if i.val < 2128 then
(if i.val < 2120 then
(if i.val < 2116 then
(if i.val < 2114 then
(if i.val < 2113 then
3035
else
3036)
else
(if i.val < 2115 then
1090
else
3037))
else
(if i.val < 2118 then
(if i.val < 2117 then
1119
else
1112)
else
(if i.val < 2119 then
1634
else
1613)))
else
(if i.val < 2124 then
(if i.val < 2122 then
(if i.val < 2121 then
2141
else
594)
else
(if i.val < 2123 then
2144
else
540))
else
(if i.val < 2126 then
(if i.val < 2125 then
1611
else
1779)
else
(if i.val < 2127 then
3223
else
3224))))
else
(if i.val < 2136 then
(if i.val < 2132 then
(if i.val < 2130 then
(if i.val < 2129 then
1217
else
1221)
else
(if i.val < 2131 then
1214
else
3225))
else
(if i.val < 2134 then
(if i.val < 2133 then
3226
else
3228)
else
(if i.val < 2135 then
2788
else
2139)))
else
(if i.val < 2140 then
(if i.val < 2138 then
(if i.val < 2137 then
3229
else
3230)
else
(if i.val < 2139 then
2147
else
1280))
else
(if i.val < 2142 then
(if i.val < 2141 then
1731
else
3231)
else
(if i.val < 2143 then
1281
else
1146)))))
else
(if i.val < 2160 then
(if i.val < 2152 then
(if i.val < 2148 then
(if i.val < 2146 then
(if i.val < 2145 then
1268
else
1269)
else
(if i.val < 2147 then
2127
else
3232))
else
(if i.val < 2150 then
(if i.val < 2149 then
3234
else
3235)
else
(if i.val < 2151 then
3236
else
3237)))
else
(if i.val < 2156 then
(if i.val < 2154 then
(if i.val < 2153 then
2157
else
3238)
else
(if i.val < 2155 then
3239
else
3240))
else
(if i.val < 2158 then
(if i.val < 2157 then
1103
else
3241)
else
(if i.val < 2159 then
3242
else
3243))))
else
(if i.val < 2168 then
(if i.val < 2164 then
(if i.val < 2162 then
(if i.val < 2161 then
2118
else
3244)
else
(if i.val < 2163 then
3246
else
3247))
else
(if i.val < 2166 then
(if i.val < 2165 then
2149
else
3248)
else
(if i.val < 2167 then
554
else
2277)))
else
(if i.val < 2172 then
(if i.val < 2170 then
(if i.val < 2169 then
1869
else
1783)
else
(if i.val < 2171 then
2895
else
3249))
else
(if i.val < 2174 then
(if i.val < 2173 then
3250
else
3251)
else
(if i.val < 2175 then
1565
else
3152)))))))
else
(if i.val < 2240 then
(if i.val < 2208 then
(if i.val < 2192 then
(if i.val < 2184 then
(if i.val < 2180 then
(if i.val < 2178 then
(if i.val < 2177 then
2091
else
2861)
else
(if i.val < 2179 then
3254
else
2958))
else
(if i.val < 2182 then
(if i.val < 2181 then
3255
else
1708)
else
(if i.val < 2183 then
3257
else
3258)))
else
(if i.val < 2188 then
(if i.val < 2186 then
(if i.val < 2185 then
836
else
3259)
else
(if i.val < 2187 then
2232
else
575))
else
(if i.val < 2190 then
(if i.val < 2189 then
1725
else
1686)
else
(if i.val < 2191 then
3261
else
2867))))
else
(if i.val < 2200 then
(if i.val < 2196 then
(if i.val < 2194 then
(if i.val < 2193 then
3262
else
840)
else
(if i.val < 2195 then
890
else
2872))
else
(if i.val < 2198 then
(if i.val < 2197 then
3263
else
3264)
else
(if i.val < 2199 then
2809
else
3265)))
else
(if i.val < 2204 then
(if i.val < 2202 then
(if i.val < 2201 then
1799
else
2862)
else
(if i.val < 2203 then
1947
else
3266))
else
(if i.val < 2206 then
(if i.val < 2205 then
2126
else
814)
else
(if i.val < 2207 then
3267
else
3128)))))
else
(if i.val < 2224 then
(if i.val < 2216 then
(if i.val < 2212 then
(if i.val < 2210 then
(if i.val < 2209 then
3268
else
3269)
else
(if i.val < 2211 then
813
else
1233))
else
(if i.val < 2214 then
(if i.val < 2213 then
1882
else
784)
else
(if i.val < 2215 then
1647
else
3413)))
else
(if i.val < 2220 then
(if i.val < 2218 then
(if i.val < 2217 then
959
else
974)
else
(if i.val < 2219 then
1689
else
3610))
else
(if i.val < 2222 then
(if i.val < 2221 then
3611
else
3612)
else
(if i.val < 2223 then
3613
else
3614))))
else
(if i.val < 2232 then
(if i.val < 2228 then
(if i.val < 2226 then
(if i.val < 2225 then
3615
else
3616)
else
(if i.val < 2227 then
3116
else
1607))
else
(if i.val < 2230 then
(if i.val < 2229 then
3617
else
3382)
else
(if i.val < 2231 then
3566
else
2797)))
else
(if i.val < 2236 then
(if i.val < 2234 then
(if i.val < 2233 then
3065
else
3618)
else
(if i.val < 2235 then
3619
else
933))
else
(if i.val < 2238 then
(if i.val < 2237 then
1670
else
3620)
else
(if i.val < 2239 then
1609
else
1786))))))
else
(if i.val < 2272 then
(if i.val < 2256 then
(if i.val < 2248 then
(if i.val < 2244 then
(if i.val < 2242 then
(if i.val < 2241 then
1231
else
3621)
else
(if i.val < 2243 then
3449
else
1196))
else
(if i.val < 2246 then
(if i.val < 2245 then
975
else
3622)
else
(if i.val < 2247 then
3366
else
3100)))
else
(if i.val < 2252 then
(if i.val < 2250 then
(if i.val < 2249 then
1949
else
2081)
else
(if i.val < 2251 then
3400
else
1200))
else
(if i.val < 2254 then
(if i.val < 2253 then
3005
else
3623)
else
(if i.val < 2255 then
2869
else
2153))))
else
(if i.val < 2264 then
(if i.val < 2260 then
(if i.val < 2258 then
(if i.val < 2257 then
3624
else
781)
else
(if i.val < 2259 then
1646
else
2894))
else
(if i.val < 2262 then
(if i.val < 2261 then
1876
else
1705)
else
(if i.val < 2263 then
3625
else
3078)))
else
(if i.val < 2268 then
(if i.val < 2266 then
(if i.val < 2265 then
1854
else
3077)
else
(if i.val < 2267 then
3626
else
3627))
else
(if i.val < 2270 then
(if i.val < 2269 then
2835
else
3628)
else
(if i.val < 2271 then
1010
else
1700)))))
else
(if i.val < 2288 then
(if i.val < 2280 then
(if i.val < 2276 then
(if i.val < 2274 then
(if i.val < 2273 then
3629
else
939)
else
(if i.val < 2275 then
3630
else
3631))
else
(if i.val < 2278 then
(if i.val < 2277 then
3632
else
2792)
else
(if i.val < 2279 then
3633
else
2985)))
else
(if i.val < 2284 then
(if i.val < 2282 then
(if i.val < 2281 then
1771
else
3634)
else
(if i.val < 2283 then
3123
else
3635))
else
(if i.val < 2286 then
(if i.val < 2285 then
1276
else
2295)
else
(if i.val < 2287 then
929
else
3636))))
else
(if i.val < 2296 then
(if i.val < 2292 then
(if i.val < 2290 then
(if i.val < 2289 then
3637
else
938)
else
(if i.val < 2291 then
3638
else
560))
else
(if i.val < 2294 then
(if i.val < 2293 then
3326
else
3147)
else
(if i.val < 2295 then
2381
else
3348)))
else
(if i.val < 2300 then
(if i.val < 2298 then
(if i.val < 2297 then
3462
else
3639)
else
(if i.val < 2299 then
2850
else
3640))
else
(if i.val < 2302 then
(if i.val < 2301 then
3641
else
3642)
else
(if i.val < 2303 then
3643
else
3644))))))))
else
(if i.val < 2432 then
(if i.val < 2368 then
(if i.val < 2336 then
(if i.val < 2320 then
(if i.val < 2312 then
(if i.val < 2308 then
(if i.val < 2306 then
(if i.val < 2305 then
3645
else
3646)
else
(if i.val < 2307 then
3167
else
3647))
else
(if i.val < 2310 then
(if i.val < 2309 then
3648
else
3649)
else
(if i.val < 2311 then
2801
else
1865)))
else
(if i.val < 2316 then
(if i.val < 2314 then
(if i.val < 2313 then
3650
else
2092)
else
(if i.val < 2315 then
1933
else
3391))
else
(if i.val < 2318 then
(if i.val < 2317 then
1701
else
3651)
else
(if i.val < 2319 then
3652
else
2190))))
else
(if i.val < 2328 then
(if i.val < 2324 then
(if i.val < 2322 then
(if i.val < 2321 then
3653
else
1738)
else
(if i.val < 2323 then
452
else
923))
else
(if i.val < 2326 then
(if i.val < 2325 then
1185
else
3513)
else
(if i.val < 2327 then
3654
else
1980)))
else
(if i.val < 2332 then
(if i.val < 2330 then
(if i.val < 2329 then
3143
else
1270)
else
(if i.val < 2331 then
2124
else
2833))
else
(if i.val < 2334 then
(if i.val < 2333 then
950
else
951)
else
(if i.val < 2335 then
432
else
532)))))
else
(if i.val < 2352 then
(if i.val < 2344 then
(if i.val < 2340 then
(if i.val < 2338 then
(if i.val < 2337 then
3655
else
2189)
else
(if i.val < 2339 then
3656
else
3657))
else
(if i.val < 2342 then
(if i.val < 2341 then
3658
else
3659)
else
(if i.val < 2343 then
2220
else
940)))
else
(if i.val < 2348 then
(if i.val < 2346 then
(if i.val < 2345 then
2793
else
457)
else
(if i.val < 2347 then
2860
else
812))
else
(if i.val < 2350 then
(if i.val < 2349 then
3660
else
3317)
else
(if i.val < 2351 then
3661
else
1877))))
else
(if i.val < 2360 then
(if i.val < 2356 then
(if i.val < 2354 then
(if i.val < 2353 then
3454
else
3539)
else
(if i.val < 2355 then
3545
else
3492))
else
(if i.val < 2358 then
(if i.val < 2357 then
3662
else
2241)
else
(if i.val < 2359 then
3663
else
3060)))
else
(if i.val < 2364 then
(if i.val < 2362 then
(if i.val < 2361 then
3664
else
3665)
else
(if i.val < 2363 then
3666
else
442))
else
(if i.val < 2366 then
(if i.val < 2365 then
458
else
3150)
else
(if i.val < 2367 then
3667
else
981))))))
else
(if i.val < 2400 then
(if i.val < 2384 then
(if i.val < 2376 then
(if i.val < 2372 then
(if i.val < 2370 then
(if i.val < 2369 then
2903
else
3668)
else
(if i.val < 2371 then
2802
else
3669))
else
(if i.val < 2374 then
(if i.val < 2373 then
1936
else
1904)
else
(if i.val < 2375 then
3053
else
3670)))
else
(if i.val < 2380 then
(if i.val < 2378 then
(if i.val < 2377 then
3671
else
3672)
else
(if i.val < 2379 then
3673
else
3674))
else
(if i.val < 2382 then
(if i.val < 2381 then
1141
else
3448)
else
(if i.val < 2383 then
1802
else
3675))))
else
(if i.val < 2392 then
(if i.val < 2388 then
(if i.val < 2386 then
(if i.val < 2385 then
2284
else
1273)
else
(if i.val < 2387 then
3270
else
886))
else
(if i.val < 2390 then
(if i.val < 2389 then
2235
else
2954)
else
(if i.val < 2391 then
2922
else
3172)))
else
(if i.val < 2396 then
(if i.val < 2394 then
(if i.val < 2393 then
3271
else
2289)
else
(if i.val < 2395 then
2273
else
3272))
else
(if i.val < 2398 then
(if i.val < 2397 then
3273
else
1641)
else
(if i.val < 2399 then
2931
else
3274)))))
else
(if i.val < 2416 then
(if i.val < 2408 then
(if i.val < 2404 then
(if i.val < 2402 then
(if i.val < 2401 then
2332
else
2333)
else
(if i.val < 2403 then
3176
else
2987))
else
(if i.val < 2406 then
(if i.val < 2405 then
2754
else
2785)
else
(if i.val < 2407 then
2216
else
3676)))
else
(if i.val < 2412 then
(if i.val < 2410 then
(if i.val < 2409 then
3521
else
587)
else
(if i.val < 2411 then
1637
else
2957))
else
(if i.val < 2414 then
(if i.val < 2413 then
1849
else
1563)
else
(if i.val < 2415 then
2217
else
1001))))
else
(if i.val < 2424 then
(if i.val < 2420 then
(if i.val < 2418 then
(if i.val < 2417 then
3533
else
1939)
else
(if i.val < 2419 then
1973
else
2367))
else
(if i.val < 2422 then
(if i.val < 2421 then
2093
else
1930)
else
(if i.val < 2423 then
2899
else
3677)))
else
(if i.val < 2428 then
(if i.val < 2426 then
(if i.val < 2425 then
3071
else
1961)
else
(if i.val < 2427 then
3518
else
2938))
else
(if i.val < 2430 then
(if i.val < 2429 then
2798
else
2936)
else
(if i.val < 2431 then
2099
else
2270)))))))
else
(if i.val < 2496 then
(if i.val < 2464 then
(if i.val < 2448 then
(if i.val < 2440 then
(if i.val < 2436 then
(if i.val < 2434 then
(if i.val < 2433 then
2098
else
3532)
else
(if i.val < 2435 then
568
else
1782))
else
(if i.val < 2438 then
(if i.val < 2437 then
3678
else
2790)
else
(if i.val < 2439 then
3679
else
2977)))
else
(if i.val < 2444 then
(if i.val < 2442 then
(if i.val < 2441 then
3680
else
3681)
else
(if i.val < 2443 then
3682
else
3355))
else
(if i.val < 2446 then
(if i.val < 2445 then
3683
else
3684)
else
(if i.val < 2447 then
3685
else
2820))))
else
(if i.val < 2456 then
(if i.val < 2452 then
(if i.val < 2450 then
(if i.val < 2449 then
3686
else
3145)
else
(if i.val < 2451 then
3687
else
859))
else
(if i.val < 2454 then
(if i.val < 2453 then
3362
else
3688)
else
(if i.val < 2455 then
2870
else
822)))
else
(if i.val < 2460 then
(if i.val < 2458 then
(if i.val < 2457 then
816
else
797)
else
(if i.val < 2459 then
3689
else
3471))
else
(if i.val < 2462 then
(if i.val < 2461 then
841
else
829)
else
(if i.val < 2463 then
2324
else
3153)))))
else
(if i.val < 2480 then
(if i.val < 2472 then
(if i.val < 2468 then
(if i.val < 2466 then
(if i.val < 2465 then
3690
else
1603)
else
(if i.val < 2467 then
3691
else
3157))
else
(if i.val < 2470 then
(if i.val < 2469 then
3692
else
1681)
else
(if i.val < 2471 then
3693
else
3694)))
else
(if i.val < 2476 then
(if i.val < 2474 then
(if i.val < 2473 then
2251
else
759)
else
(if i.val < 2475 then
3097
else
3695))
else
(if i.val < 2478 then
(if i.val < 2477 then
3696
else
2852)
else
(if i.val < 2479 then
3486
else
3697))))
else
(if i.val < 2488 then
(if i.val < 2484 then
(if i.val < 2482 then
(if i.val < 2481 then
3698
else
3514)
else
(if i.val < 2483 then
1091
else
2130))
else
(if i.val < 2486 then
(if i.val < 2485 then
3699
else
3700)
else
(if i.val < 2487 then
2128
else
3089)))
else
(if i.val < 2492 then
(if i.val < 2490 then
(if i.val < 2489 then
984
else
3156)
else
(if i.val < 2491 then
3701
else
3702))
else
(if i.val < 2494 then
(if i.val < 2493 then
3323
else
3703)
else
(if i.val < 2495 then
3704
else
3705))))))
else
(if i.val < 2528 then
(if i.val < 2512 then
(if i.val < 2504 then
(if i.val < 2500 then
(if i.val < 2498 then
(if i.val < 2497 then
2240
else
3706)
else
(if i.val < 2499 then
2211
else
3515))
else
(if i.val < 2502 then
(if i.val < 2501 then
755
else
856)
else
(if i.val < 2503 then
892
else
778)))
else
(if i.val < 2508 then
(if i.val < 2506 then
(if i.val < 2505 then
3707
else
3708)
else
(if i.val < 2507 then
3709
else
3710))
else
(if i.val < 2510 then
(if i.val < 2509 then
3444
else
3711)
else
(if i.val < 2511 then
3291
else
2995))))
else
(if i.val < 2520 then
(if i.val < 2516 then
(if i.val < 2514 then
(if i.val < 2513 then
3712
else
3713)
else
(if i.val < 2515 then
3098
else
3714))
else
(if i.val < 2518 then
(if i.val < 2517 then
3541
else
3289)
else
(if i.val < 2519 then
3715
else
3716)))
else
(if i.val < 2524 then
(if i.val < 2522 then
(if i.val < 2521 then
3717
else
3718)
else
(if i.val < 2523 then
3512
else
3719))
else
(if i.val < 2526 then
(if i.val < 2525 then
3487
else
2774)
else
(if i.val < 2527 then
2142
else
427)))))
else
(if i.val < 2544 then
(if i.val < 2536 then
(if i.val < 2532 then
(if i.val < 2530 then
(if i.val < 2529 then
430
else
431)
else
(if i.val < 2531 then
433
else
438))
else
(if i.val < 2534 then
(if i.val < 2533 then
439
else
440)
else
(if i.val < 2535 then
444
else
448)))
else
(if i.val < 2540 then
(if i.val < 2538 then
(if i.val < 2537 then
449
else
530)
else
(if i.val < 2539 then
533
else
535))
else
(if i.val < 2542 then
(if i.val < 2541 then
543
else
547)
else
(if i.val < 2543 then
550
else
551))))
else
(if i.val < 2552 then
(if i.val < 2548 then
(if i.val < 2546 then
(if i.val < 2545 then
552
else
553)
else
(if i.val < 2547 then
555
else
556))
else
(if i.val < 2550 then
(if i.val < 2549 then
557
else
559)
else
(if i.val < 2551 then
564
else
567)))
else
(if i.val < 2556 then
(if i.val < 2554 then
(if i.val < 2553 then
569
else
570)
else
(if i.val < 2555 then
571
else
572))
else
(if i.val < 2558 then
(if i.val < 2557 then
576
else
578)
else
(if i.val < 2559 then
580
else
582)))))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row18_cosetGeneratorNextColumn1Part0005 : Fin 4320 → Fin 4320 :=
  fun i => (if i.val < 2816 then
(if i.val < 2688 then
(if i.val < 2624 then
(if i.val < 2592 then
(if i.val < 2576 then
(if i.val < 2568 then
(if i.val < 2564 then
(if i.val < 2562 then
(if i.val < 2561 then
583
else
584)
else
(if i.val < 2563 then
586
else
589))
else
(if i.val < 2566 then
(if i.val < 2565 then
590
else
592)
else
(if i.val < 2567 then
749
else
750)))
else
(if i.val < 2572 then
(if i.val < 2570 then
(if i.val < 2569 then
752
else
753)
else
(if i.val < 2571 then
754
else
756))
else
(if i.val < 2574 then
(if i.val < 2573 then
757
else
760)
else
(if i.val < 2575 then
761
else
762))))
else
(if i.val < 2584 then
(if i.val < 2580 then
(if i.val < 2578 then
(if i.val < 2577 then
764
else
765)
else
(if i.val < 2579 then
766
else
768))
else
(if i.val < 2582 then
(if i.val < 2581 then
773
else
774)
else
(if i.val < 2583 then
775
else
776)))
else
(if i.val < 2588 then
(if i.val < 2586 then
(if i.val < 2585 then
779
else
782)
else
(if i.val < 2587 then
787
else
790))
else
(if i.val < 2590 then
(if i.val < 2589 then
794
else
798)
else
(if i.val < 2591 then
799
else
800)))))
else
(if i.val < 2608 then
(if i.val < 2600 then
(if i.val < 2596 then
(if i.val < 2594 then
(if i.val < 2593 then
801
else
805)
else
(if i.val < 2595 then
809
else
811))
else
(if i.val < 2598 then
(if i.val < 2597 then
818
else
821)
else
(if i.val < 2599 then
828
else
831)))
else
(if i.val < 2604 then
(if i.val < 2602 then
(if i.val < 2601 then
835
else
844)
else
(if i.val < 2603 then
845
else
846))
else
(if i.val < 2606 then
(if i.val < 2605 then
848
else
849)
else
(if i.val < 2607 then
850
else
851))))
else
(if i.val < 2616 then
(if i.val < 2612 then
(if i.val < 2610 then
(if i.val < 2609 then
852
else
853)
else
(if i.val < 2611 then
855
else
858))
else
(if i.val < 2614 then
(if i.val < 2613 then
862
else
867)
else
(if i.val < 2615 then
870
else
871)))
else
(if i.val < 2620 then
(if i.val < 2618 then
(if i.val < 2617 then
872
else
877)
else
(if i.val < 2619 then
880
else
887))
else
(if i.val < 2622 then
(if i.val < 2621 then
888
else
889)
else
(if i.val < 2623 then
894
else
3193))))))
else
(if i.val < 2656 then
(if i.val < 2640 then
(if i.val < 2632 then
(if i.val < 2628 then
(if i.val < 2626 then
(if i.val < 2625 then
2174
else
3720)
else
(if i.val < 2627 then
3721
else
1960))
else
(if i.val < 2630 then
(if i.val < 2629 then
3338
else
3477)
else
(if i.val < 2631 then
3722
else
3723)))
else
(if i.val < 2636 then
(if i.val < 2634 then
(if i.val < 2633 then
3154
else
2978)
else
(if i.val < 2635 then
3724
else
1768))
else
(if i.val < 2638 then
(if i.val < 2637 then
1575
else
1250)
else
(if i.val < 2639 then
2794
else
2886))))
else
(if i.val < 2648 then
(if i.val < 2644 then
(if i.val < 2642 then
(if i.val < 2641 then
3377
else
3102)
else
(if i.val < 2643 then
3419
else
3522))
else
(if i.val < 2646 then
(if i.val < 2645 then
1770
else
2227)
else
(if i.val < 2647 then
3725
else
3726)))
else
(if i.val < 2652 then
(if i.val < 2650 then
(if i.val < 2649 then
2119
else
2829)
else
(if i.val < 2651 then
1929
else
2855))
else
(if i.val < 2654 then
(if i.val < 2653 then
3727
else
1711)
else
(if i.val < 2655 then
3728
else
2878)))))
else
(if i.val < 2672 then
(if i.val < 2664 then
(if i.val < 2660 then
(if i.val < 2658 then
(if i.val < 2657 then
3729
else
1680)
else
(if i.val < 2659 then
2824
else
3730))
else
(if i.val < 2662 then
(if i.val < 2661 then
2072
else
2949)
else
(if i.val < 2663 then
3284
else
2836)))
else
(if i.val < 2668 then
(if i.val < 2666 then
(if i.val < 2665 then
3731
else
2214)
else
(if i.val < 2667 then
2810
else
3732))
else
(if i.val < 2670 then
(if i.val < 2669 then
2923
else
2095)
else
(if i.val < 2671 then
1658
else
3733))))
else
(if i.val < 2680 then
(if i.val < 2676 then
(if i.val < 2674 then
(if i.val < 2673 then
2088
else
3414)
else
(if i.val < 2675 then
1251
else
1194))
else
(if i.val < 2678 then
(if i.val < 2677 then
3734
else
3735)
else
(if i.val < 2679 then
3736
else
3381)))
else
(if i.val < 2684 then
(if i.val < 2682 then
(if i.val < 2681 then
2236
else
1893)
else
(if i.val < 2683 then
3538
else
3384))
else
(if i.val < 2686 then
(if i.val < 2685 then
2789
else
3407)
else
(if i.val < 2687 then
1907
else
2218)))))))
else
(if i.val < 2752 then
(if i.val < 2720 then
(if i.val < 2704 then
(if i.val < 2696 then
(if i.val < 2692 then
(if i.val < 2690 then
(if i.val < 2689 then
3737
else
3498)
else
(if i.val < 2691 then
1138
else
1632))
else
(if i.val < 2694 then
(if i.val < 2693 then
2825
else
2893)
else
(if i.val < 2695 then
3738
else
962)))
else
(if i.val < 2700 then
(if i.val < 2698 then
(if i.val < 2697 then
2271
else
2316)
else
(if i.val < 2699 then
3739
else
2994))
else
(if i.val < 2702 then
(if i.val < 2701 then
2100
else
2102)
else
(if i.val < 2703 then
2111
else
2181))))
else
(if i.val < 2712 then
(if i.val < 2708 then
(if i.val < 2706 then
(if i.val < 2705 then
2912
else
3740)
else
(if i.val < 2707 then
3476
else
1962))
else
(if i.val < 2710 then
(if i.val < 2709 then
2999
else
3741)
else
(if i.val < 2711 then
3742
else
2188)))
else
(if i.val < 2716 then
(if i.val < 2714 then
(if i.val < 2713 then
3743
else
3744)
else
(if i.val < 2715 then
2831
else
1618))
else
(if i.val < 2718 then
(if i.val < 2717 then
1900
else
2140)
else
(if i.val < 2719 then
1852
else
953)))))
else
(if i.val < 2736 then
(if i.val < 2728 then
(if i.val < 2724 then
(if i.val < 2722 then
(if i.val < 2721 then
3745
else
1958)
else
(if i.val < 2723 then
3746
else
2770))
else
(if i.val < 2726 then
(if i.val < 2725 then
3361
else
1685)
else
(if i.val < 2727 then
3087
else
3747)))
else
(if i.val < 2732 then
(if i.val < 2730 then
(if i.val < 2729 then
3508
else
3748)
else
(if i.val < 2731 then
2759
else
1582))
else
(if i.val < 2734 then
(if i.val < 2733 then
3453
else
2871)
else
(if i.val < 2735 then
3749
else
2280))))
else
(if i.val < 2744 then
(if i.val < 2740 then
(if i.val < 2738 then
(if i.val < 2737 then
1682
else
3011)
else
(if i.val < 2739 then
3750
else
2077))
else
(if i.val < 2742 then
(if i.val < 2741 then
2125
else
1898)
else
(if i.val < 2743 then
2169
else
2239)))
else
(if i.val < 2748 then
(if i.val < 2746 then
(if i.val < 2745 then
3751
else
1009)
else
(if i.val < 2747 then
3401
else
2786))
else
(if i.val < 2750 then
(if i.val < 2749 then
964
else
3752)
else
(if i.val < 2751 then
2200
else
2382))))))
else
(if i.val < 2784 then
(if i.val < 2768 then
(if i.val < 2760 then
(if i.val < 2756 then
(if i.val < 2754 then
(if i.val < 2753 then
3115
else
2983)
else
(if i.val < 2755 then
957
else
2302))
else
(if i.val < 2758 then
(if i.val < 2757 then
3753
else
3436)
else
(if i.val < 2759 then
3754
else
1759)))
else
(if i.val < 2764 then
(if i.val < 2762 then
(if i.val < 2761 then
3755
else
3756)
else
(if i.val < 2763 then
3162
else
3516))
else
(if i.val < 2766 then
(if i.val < 2765 then
3757
else
3091)
else
(if i.val < 2767 then
3344
else
3507))))
else
(if i.val < 2776 then
(if i.val < 2772 then
(if i.val < 2770 then
(if i.val < 2769 then
3517
else
3526)
else
(if i.val < 2771 then
1744
else
3758))
else
(if i.val < 2774 then
(if i.val < 2773 then
2883
else
2778)
else
(if i.val < 2775 then
1279
else
2819)))
else
(if i.val < 2780 then
(if i.val < 2778 then
(if i.val < 2777 then
2973
else
3759)
else
(if i.val < 2779 then
3760
else
3761))
else
(if i.val < 2782 then
(if i.val < 2781 then
3762
else
2930)
else
(if i.val < 2783 then
2800
else
3475)))))
else
(if i.val < 2800 then
(if i.val < 2792 then
(if i.val < 2788 then
(if i.val < 2786 then
(if i.val < 2785 then
3505
else
958)
else
(if i.val < 2787 then
1795
else
2175))
else
(if i.val < 2790 then
(if i.val < 2789 then
1576
else
1683)
else
(if i.val < 2791 then
1149
else
3763)))
else
(if i.val < 2796 then
(if i.val < 2794 then
(if i.val < 2793 then
2167
else
1566)
else
(if i.val < 2795 then
1594
else
3764))
else
(if i.val < 2798 then
(if i.val < 2797 then
3765
else
3502)
else
(if i.val < 2799 then
1004
else
3766))))
else
(if i.val < 2808 then
(if i.val < 2804 then
(if i.val < 2802 then
(if i.val < 2801 then
3767
else
3768)
else
(if i.val < 2803 then
3769
else
2882))
else
(if i.val < 2806 then
(if i.val < 2805 then
2991
else
3003)
else
(if i.val < 2807 then
2336
else
3489)))
else
(if i.val < 2812 then
(if i.val < 2810 then
(if i.val < 2809 then
3770
else
2980)
else
(if i.val < 2811 then
1649
else
3771))
else
(if i.val < 2814 then
(if i.val < 2813 then
3772
else
3563)
else
(if i.val < 2815 then
3773
else
3774))))))))
else
(if i.val < 2944 then
(if i.val < 2880 then
(if i.val < 2848 then
(if i.val < 2832 then
(if i.val < 2824 then
(if i.val < 2820 then
(if i.val < 2818 then
(if i.val < 2817 then
3775
else
1989)
else
(if i.val < 2819 then
3180
else
3776))
else
(if i.val < 2822 then
(if i.val < 2821 then
1165
else
2172)
else
(if i.val < 2823 then
2815
else
1081)))
else
(if i.val < 2828 then
(if i.val < 2826 then
(if i.val < 2825 then
1628
else
1696)
else
(if i.val < 2827 then
3777
else
3457))
else
(if i.val < 2830 then
(if i.val < 2829 then
1921
else
1614)
else
(if i.val < 2831 then
3504
else
1728))))
else
(if i.val < 2840 then
(if i.val < 2836 then
(if i.val < 2834 then
(if i.val < 2833 then
2301
else
1574)
else
(if i.val < 2835 then
3778
else
3079))
else
(if i.val < 2838 then
(if i.val < 2837 then
1644
else
3779)
else
(if i.val < 2839 then
1116
else
2082)))
else
(if i.val < 2844 then
(if i.val < 2842 then
(if i.val < 2841 then
3780
else
2837)
else
(if i.val < 2843 then
3299
else
2920))
else
(if i.val < 2846 then
(if i.val < 2845 then
3000
else
2359)
else
(if i.val < 2847 then
2379
else
2763)))))
else
(if i.val < 2864 then
(if i.val < 2856 then
(if i.val < 2852 then
(if i.val < 2850 then
(if i.val < 2849 then
2374
else
3393)
else
(if i.val < 2851 then
2963
else
3459))
else
(if i.val < 2854 then
(if i.val < 2853 then
1205
else
3781)
else
(if i.val < 2855 then
2889
else
1616)))
else
(if i.val < 2860 then
(if i.val < 2858 then
(if i.val < 2857 then
3782
else
3783)
else
(if i.val < 2859 then
3055
else
2799))
else
(if i.val < 2862 then
(if i.val < 2861 then
2090
else
3784)
else
(if i.val < 2863 then
3785
else
3786))))
else
(if i.val < 2872 then
(if i.val < 2868 then
(if i.val < 2866 then
(if i.val < 2865 then
3787
else
3375)
else
(if i.val < 2867 then
2784
else
3788))
else
(if i.val < 2870 then
(if i.val < 2869 then
1952
else
1914)
else
(if i.val < 2871 then
1176
else
1766)))
else
(if i.val < 2876 then
(if i.val < 2874 then
(if i.val < 2873 then
1709
else
3478)
else
(if i.val < 2875 then
3789
else
3497))
else
(if i.val < 2878 then
(if i.val < 2877 then
3790
else
3403)
else
(if i.val < 2879 then
1623
else
2165))))))
else
(if i.val < 2912 then
(if i.val < 2896 then
(if i.val < 2888 then
(if i.val < 2884 then
(if i.val < 2882 then
(if i.val < 2881 then
2246
else
2905)
else
(if i.val < 2883 then
2909
else
3791))
else
(if i.val < 2886 then
(if i.val < 2885 then
3524
else
3525)
else
(if i.val < 2887 then
1597
else
2842)))
else
(if i.val < 2892 then
(if i.val < 2890 then
(if i.val < 2889 then
2853
else
3792)
else
(if i.val < 2891 then
3551
else
3793))
else
(if i.val < 2894 then
(if i.val < 2893 then
3794
else
1697)
else
(if i.val < 2895 then
3795
else
3405))))
else
(if i.val < 2904 then
(if i.val < 2900 then
(if i.val < 2898 then
(if i.val < 2897 then
3796
else
3797)
else
(if i.val < 2899 then
3798
else
991))
else
(if i.val < 2902 then
(if i.val < 2901 then
3411
else
3799)
else
(if i.val < 2903 then
3800
else
3801)))
else
(if i.val < 2908 then
(if i.val < 2906 then
(if i.val < 2905 then
3802
else
3803)
else
(if i.val < 2907 then
3804
else
3805))
else
(if i.val < 2910 then
(if i.val < 2909 then
3806
else
2803)
else
(if i.val < 2911 then
3543
else
3807)))))
else
(if i.val < 2928 then
(if i.val < 2920 then
(if i.val < 2916 then
(if i.val < 2914 then
(if i.val < 2913 then
1714
else
3808)
else
(if i.val < 2915 then
3535
else
2874))
else
(if i.val < 2918 then
(if i.val < 2917 then
3809
else
3810)
else
(if i.val < 2919 then
2203
else
3811)))
else
(if i.val < 2924 then
(if i.val < 2922 then
(if i.val < 2921 then
3812
else
2281)
else
(if i.val < 2923 then
935
else
1651))
else
(if i.val < 2926 then
(if i.val < 2925 then
3424
else
3059)
else
(if i.val < 2927 then
3057
else
1887))))
else
(if i.val < 2936 then
(if i.val < 2932 then
(if i.val < 2930 then
(if i.val < 2929 then
3813
else
2362)
else
(if i.val < 2931 then
3185
else
944))
else
(if i.val < 2934 then
(if i.val < 2933 then
3814
else
3815)
else
(if i.val < 2935 then
2766
else
1005)))
else
(if i.val < 2940 then
(if i.val < 2938 then
(if i.val < 2937 then
1006
else
989)
else
(if i.val < 2939 then
999
else
1007))
else
(if i.val < 2942 then
(if i.val < 2941 then
982
else
3107)
else
(if i.val < 2943 then
2373
else
2762)))))))
else
(if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
3189
else
3177)
else
(if i.val < 2947 then
1108
else
3816))
else
(if i.val < 2950 then
(if i.val < 2949 then
3127
else
1633)
else
(if i.val < 2951 then
3817
else
2233)))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
2229
else
3818)
else
(if i.val < 2955 then
934
else
968))
else
(if i.val < 2958 then
(if i.val < 2957 then
969
else
970)
else
(if i.val < 2959 then
971
else
2761))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
2199
else
3819)
else
(if i.val < 2963 then
3820
else
2298))
else
(if i.val < 2966 then
(if i.val < 2965 then
2863
else
3351)
else
(if i.val < 2967 then
3499
else
3109)))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
3390
else
3332)
else
(if i.val < 2971 then
3536
else
3437))
else
(if i.val < 2974 then
(if i.val < 2973 then
1880
else
3821)
else
(if i.val < 2975 then
3822
else
3404)))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
2811
else
1156)
else
(if i.val < 2979 then
1588
else
2768))
else
(if i.val < 2982 then
(if i.val < 2981 then
2198
else
3823)
else
(if i.val < 2983 then
3824
else
2997)))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
2804
else
1626)
else
(if i.val < 2987 then
3825
else
955))
else
(if i.val < 2990 then
(if i.val < 2989 then
3826
else
3337)
else
(if i.val < 2991 then
3827
else
2984))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
3828
else
1870)
else
(if i.val < 2995 then
1703
else
1254))
else
(if i.val < 2998 then
(if i.val < 2997 then
1872
else
2753)
else
(if i.val < 2999 then
3829
else
1719)))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
3830
else
2968)
else
(if i.val < 3003 then
3831
else
3832))
else
(if i.val < 3006 then
(if i.val < 3005 then
1920
else
1775)
else
(if i.val < 3007 then
3833
else
1241))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
3431
else
1937)
else
(if i.val < 3011 then
3484
else
1776))
else
(if i.val < 3014 then
(if i.val < 3013 then
2813
else
2161)
else
(if i.val < 3015 then
994
else
1059)))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
1060
else
1064)
else
(if i.val < 3019 then
1065
else
3988))
else
(if i.val < 3022 then
(if i.val < 3021 then
3321
else
3898)
else
(if i.val < 3023 then
2249
else
2839))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
1170
else
2176)
else
(if i.val < 3027 then
4076
else
4024))
else
(if i.val < 3030 then
(if i.val < 3029 then
3282
else
3994)
else
(if i.val < 3031 then
4077
else
3094)))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
3287
else
4078)
else
(if i.val < 3035 then
1113
else
4022))
else
(if i.val < 3038 then
(if i.val < 3037 then
3311
else
1888)
else
(if i.val < 3039 then
924
else
927)))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
4003
else
3529)
else
(if i.val < 3043 then
3144
else
4004))
else
(if i.val < 3046 then
(if i.val < 3045 then
2264
else
1077)
else
(if i.val < 3047 then
2076
else
1125)))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
1258
else
1721)
else
(if i.val < 3051 then
3170
else
3171))
else
(if i.val < 3054 then
(if i.val < 3053 then
1891
else
2848)
else
(if i.val < 3055 then
1901
else
3943))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
2941
else
1935)
else
(if i.val < 3059 then
3909
else
3395))
else
(if i.val < 3062 then
(if i.val < 3061 then
2845
else
4005)
else
(if i.val < 3063 then
4006
else
3523)))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
3396
else
2186)
else
(if i.val < 3067 then
3923
else
3984))
else
(if i.val < 3070 then
(if i.val < 3069 then
4206
else
4107)
else
(if i.val < 3071 then
4011
else
995)))))))))

end HodgeLean.Foundations.Program

end
