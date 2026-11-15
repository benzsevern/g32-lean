import Mathlib.Data.Fin.Basic
import HodgeLean.Foundations.Program.G32PropFourSixPacked1030
import HodgeLean.Foundations.Program.G32PropFourSixPacked1039
import HodgeLean.Foundations.Program.G32PropFourSixPacked1040
import HodgeLean.Foundations.Program.G32PropFourSixPacked1041
import HodgeLean.Foundations.Program.G32PropFourSixPacked1042
import HodgeLean.Foundations.Program.G32PropFourSixPacked1043
import HodgeLean.Foundations.Program.G32PropFourSixPacked1035
import HodgeLean.Foundations.Program.G32PropFourSixPacked1036
import HodgeLean.Foundations.Program.G32PropFourSixPacked1037
import HodgeLean.Foundations.Program.G32PropFourSixPacked1034
import HodgeLean.Foundations.Program.G32PropFourSixPacked1031
import HodgeLean.Foundations.Program.G32PropFourSixPacked1029
import HodgeLean.Foundations.Program.G32PropFourSixPacked1032
import HodgeLean.Foundations.Program.G32PropFourSixPacked1038
import HodgeLean.Foundations.Program.G32PropFourSixPacked1033
import HodgeLean.Foundations.Program.G32PropFourSixPacked0494
import HodgeLean.Foundations.Program.G32PropFourSixArchiveReverse

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0023 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3008 then
(if i.val < 2976 then
(if i.val < 2960 then
(if i.val < 2952 then
(if i.val < 2948 then
(if i.val < 2946 then
(if i.val < 2945 then
[2, 1, 0, 3, 3, 2, 1, 1]
else
[2, 1, 1, 0, 0, 2, 1, 3])
else
(if i.val < 2947 then
[2, 1, 1, 0, 0, 3, 0, 0]
else
[2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 2950 then
(if i.val < 2949 then
[2, 1, 1, 0, 0, 3, 2, 1]
else
[2, 1, 1, 0, 0, 3, 2, 2])
else
(if i.val < 2951 then
[2, 1, 1, 0, 0, 3, 3, 2]
else
[2, 1, 1, 0, 2, 1, 1, 3])))
else
(if i.val < 2956 then
(if i.val < 2954 then
(if i.val < 2953 then
[2, 1, 1, 0, 2, 1, 3, 2]
else
[2, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 2955 then
[2, 1, 1, 0, 2, 3, 2, 1]
else
[2, 1, 1, 0, 2, 3, 3, 2]))
else
(if i.val < 2958 then
(if i.val < 2957 then
[2, 1, 1, 0, 3, 0, 0, 3]
else
[2, 1, 1, 0, 3, 0, 1, 2])
else
(if i.val < 2959 then
[2, 1, 1, 0, 3, 0, 2, 1]
else
[2, 1, 1, 0, 3, 0, 2, 2]))))
else
(if i.val < 2968 then
(if i.val < 2964 then
(if i.val < 2962 then
(if i.val < 2961 then
[2, 1, 1, 0, 3, 2, 1, 1]
else
[2, 1, 1, 0, 3, 2, 2, 3])
else
(if i.val < 2963 then
[2, 1, 1, 2, 3, 0, 1, 2]
else
[2, 1, 1, 2, 3, 2, 1, 1]))
else
(if i.val < 2966 then
(if i.val < 2965 then
[2, 1, 1, 2, 3, 2, 2, 3]
else
[2, 1, 1, 3, 0, 0, 1, 1])
else
(if i.val < 2967 then
[2, 1, 1, 3, 0, 1, 2, 1]
else
[2, 1, 1, 3, 0, 1, 2, 2])))
else
(if i.val < 2972 then
(if i.val < 2970 then
(if i.val < 2969 then
[2, 1, 1, 3, 0, 1, 2, 3]
else
[2, 1, 1, 3, 0, 2, 1, 1])
else
(if i.val < 2971 then
[2, 1, 1, 3, 3, 0, 1, 2]
else
[2, 1, 3, 0, 0, 1, 1, 3]))
else
(if i.val < 2974 then
(if i.val < 2973 then
[2, 1, 3, 0, 0, 1, 2, 1]
else
[2, 1, 3, 0, 0, 1, 2, 3])
else
(if i.val < 2975 then
[2, 1, 3, 0, 0, 2, 2, 1]
else
[2, 1, 3, 0, 0, 2, 2, 3])))))
else
(if i.val < 2992 then
(if i.val < 2984 then
(if i.val < 2980 then
(if i.val < 2978 then
(if i.val < 2977 then
[2, 1, 3, 0, 0, 3, 2, 1]
else
[2, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 2979 then
[2, 1, 3, 0, 2, 2, 3, 3]
else
[2, 1, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 2982 then
(if i.val < 2981 then
[2, 1, 3, 2, 2, 1, 1, 3]
else
[2, 1, 3, 2, 2, 1, 3, 2])
else
(if i.val < 2983 then
[2, 1, 3, 2, 2, 3, 0, 0]
else
[2, 1, 3, 2, 2, 3, 0, 1])))
else
(if i.val < 2988 then
(if i.val < 2986 then
(if i.val < 2985 then
[2, 1, 3, 3, 0, 0, 2, 1]
else
[2, 1, 3, 3, 0, 1, 2, 3])
else
(if i.val < 2987 then
[2, 1, 3, 3, 0, 2, 1, 3]
else
[2, 1, 3, 3, 0, 2, 2, 3]))
else
(if i.val < 2990 then
(if i.val < 2989 then
[2, 1, 3, 3, 0, 2, 3, 3]
else
[2, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 2991 then
[2, 1, 3, 3, 2, 1, 0, 3]
else
[2, 1, 3, 3, 2, 2, 1, 1]))))
else
(if i.val < 3000 then
(if i.val < 2996 then
(if i.val < 2994 then
(if i.val < 2993 then
[2, 2, 1, 0, 0, 1, 2, 3]
else
[2, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 2995 then
[2, 2, 1, 0, 3, 0, 0, 1]
else
[2, 2, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 2998 then
(if i.val < 2997 then
[2, 2, 1, 0, 3, 0, 2, 1]
else
[2, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 2999 then
[2, 2, 1, 0, 3, 2, 1, 1]
else
[2, 2, 1, 0, 3, 2, 2, 3])))
else
(if i.val < 3004 then
(if i.val < 3002 then
(if i.val < 3001 then
[2, 2, 1, 1, 0, 0, 3, 0]
else
[2, 2, 1, 1, 0, 3, 0, 1])
else
(if i.val < 3003 then
[2, 2, 1, 1, 0, 3, 2, 1]
else
[2, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 3006 then
(if i.val < 3005 then
[2, 2, 1, 1, 3, 0, 1, 2]
else
[2, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 3007 then
[2, 2, 1, 3, 0, 0, 2, 1]
else
[2, 2, 1, 3, 0, 0, 2, 3]))))))
else
(if i.val < 3040 then
(if i.val < 3024 then
(if i.val < 3016 then
(if i.val < 3012 then
(if i.val < 3010 then
(if i.val < 3009 then
[2, 2, 1, 3, 0, 1, 2, 1]
else
[2, 2, 1, 3, 0, 1, 2, 2])
else
(if i.val < 3011 then
[2, 2, 1, 3, 0, 1, 2, 3]
else
[2, 2, 1, 3, 2, 1, 0, 3]))
else
(if i.val < 3014 then
(if i.val < 3013 then
[2, 2, 1, 3, 2, 2, 1, 1]
else
[2, 2, 1, 3, 2, 2, 1, 3])
else
(if i.val < 3015 then
[2, 2, 1, 3, 3, 0, 1, 2]
else
[2, 2, 1, 3, 3, 0, 2, 3])))
else
(if i.val < 3020 then
(if i.val < 3018 then
(if i.val < 3017 then
[2, 2, 1, 3, 3, 2, 2, 1]
else
[2, 2, 3, 0, 0, 1, 1, 3])
else
(if i.val < 3019 then
[2, 2, 3, 0, 0, 1, 2, 1]
else
[2, 2, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 3022 then
(if i.val < 3021 then
[2, 2, 3, 0, 0, 2, 2, 1]
else
[2, 2, 3, 0, 0, 2, 2, 3])
else
(if i.val < 3023 then
[2, 2, 3, 0, 0, 3, 2, 2]
else
[2, 2, 3, 0, 1, 1, 2, 2]))))
else
(if i.val < 3032 then
(if i.val < 3028 then
(if i.val < 3026 then
(if i.val < 3025 then
[2, 2, 3, 0, 1, 2, 2, 1]
else
[2, 2, 3, 0, 2, 1, 0, 3])
else
(if i.val < 3027 then
[2, 2, 3, 0, 2, 1, 1, 3]
else
[2, 2, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 3030 then
(if i.val < 3029 then
[2, 2, 3, 2, 1, 0, 0, 3]
else
[2, 2, 3, 2, 1, 0, 3, 3])
else
(if i.val < 3031 then
[2, 2, 3, 2, 1, 1, 2, 3]
else
[2, 2, 3, 2, 2, 1, 0, 3])))
else
(if i.val < 3036 then
(if i.val < 3034 then
(if i.val < 3033 then
[2, 2, 3, 2, 2, 1, 1, 3]
else
[2, 2, 3, 2, 2, 1, 3, 2])
else
(if i.val < 3035 then
[2, 2, 3, 3, 0, 0, 2, 3]
else
[2, 2, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 3038 then
(if i.val < 3037 then
[2, 2, 3, 3, 0, 2, 2, 3]
else
[2, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 3039 then
[2, 3, 0, 0, 1, 1, 2, 2]
else
[2, 3, 0, 0, 1, 2, 1, 3])))))
else
(if i.val < 3056 then
(if i.val < 3048 then
(if i.val < 3044 then
(if i.val < 3042 then
(if i.val < 3041 then
[2, 3, 0, 0, 1, 2, 3, 0]
else
[2, 3, 0, 0, 1, 2, 3, 2])
else
(if i.val < 3043 then
[2, 3, 0, 0, 1, 3, 0, 0]
else
[2, 3, 0, 0, 1, 3, 2, 1]))
else
(if i.val < 3046 then
(if i.val < 3045 then
[2, 3, 0, 0, 2, 1, 0, 0]
else
[2, 3, 0, 0, 2, 1, 1, 3])
else
(if i.val < 3047 then
[2, 3, 0, 0, 2, 2, 1, 1]
else
[2, 3, 0, 0, 2, 2, 3, 2])))
else
(if i.val < 3052 then
(if i.val < 3050 then
(if i.val < 3049 then
[2, 3, 0, 0, 2, 3, 3, 2]
else
[2, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 3051 then
[2, 3, 0, 1, 1, 0, 2, 2]
else
[2, 3, 0, 1, 1, 0, 3, 3]))
else
(if i.val < 3054 then
(if i.val < 3053 then
[2, 3, 0, 1, 1, 2, 1, 1]
else
[2, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 3055 then
[2, 3, 0, 1, 1, 2, 3, 3]
else
[2, 3, 0, 1, 2, 1, 1, 3]))))
else
(if i.val < 3064 then
(if i.val < 3060 then
(if i.val < 3058 then
(if i.val < 3057 then
[2, 3, 0, 1, 2, 2, 1, 3]
else
[2, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 3059 then
[2, 3, 0, 1, 2, 3, 0, 0]
else
[2, 3, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 3062 then
(if i.val < 3061 then
[2, 3, 0, 2, 1, 0, 3, 2]
else
[2, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 3063 then
[2, 3, 0, 2, 1, 1, 2, 3]
else
[2, 3, 0, 2, 2, 1, 1, 3])))
else
(if i.val < 3068 then
(if i.val < 3066 then
(if i.val < 3065 then
[2, 3, 0, 2, 2, 3, 0, 1]
else
[2, 3, 2, 1, 0, 3, 3, 0])
else
(if i.val < 3067 then
[2, 3, 2, 1, 1, 0, 3, 3]
else
[2, 3, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 3070 then
(if i.val < 3069 then
[2, 3, 2, 2, 1, 1, 3, 2]
else
[2, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 3071 then
[2, 3, 2, 2, 3, 0, 0, 3]
else
[2, 3, 2, 2, 3, 0, 1, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0024 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3136 then
(if i.val < 3104 then
(if i.val < 3088 then
(if i.val < 3080 then
(if i.val < 3076 then
(if i.val < 3074 then
(if i.val < 3073 then
[2, 3, 3, 0, 0, 1, 2, 1]
else
[2, 3, 3, 0, 0, 2, 1, 1])
else
(if i.val < 3075 then
[2, 3, 3, 0, 1, 1, 0, 3]
else
[2, 3, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 3078 then
(if i.val < 3077 then
[2, 3, 3, 0, 1, 2, 3, 0]
else
[2, 3, 3, 0, 2, 1, 0, 3])
else
(if i.val < 3079 then
[2, 3, 3, 0, 2, 1, 1, 3]
else
[2, 3, 3, 0, 2, 1, 3, 2])))
else
(if i.val < 3084 then
(if i.val < 3082 then
(if i.val < 3081 then
[2, 3, 3, 0, 2, 2, 3, 3]
else
[2, 3, 3, 2, 1, 0, 3, 3])
else
(if i.val < 3083 then
[2, 3, 3, 2, 1, 1, 0, 3]
else
[2, 3, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 3086 then
(if i.val < 3085 then
[3, 0, 0, 1, 1, 2, 1, 3]
else
[3, 0, 0, 1, 1, 2, 2, 1])
else
(if i.val < 3087 then
[3, 0, 0, 1, 1, 3, 2, 2]
else
[3, 0, 0, 1, 2, 1, 1, 3]))))
else
(if i.val < 3096 then
(if i.val < 3092 then
(if i.val < 3090 then
(if i.val < 3089 then
[3, 0, 0, 1, 2, 1, 3, 0]
else
[3, 0, 0, 1, 2, 2, 1, 3])
else
(if i.val < 3091 then
[3, 0, 0, 1, 2, 3, 0, 1]
else
[3, 0, 0, 1, 2, 3, 2, 1]))
else
(if i.val < 3094 then
(if i.val < 3093 then
[3, 0, 0, 1, 2, 3, 3, 2]
else
[3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 3095 then
[3, 0, 0, 2, 1, 1, 0, 0]
else
[3, 0, 0, 2, 1, 1, 0, 3])))
else
(if i.val < 3100 then
(if i.val < 3098 then
(if i.val < 3097 then
[3, 0, 0, 2, 1, 1, 3, 3]
else
[3, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 3099 then
[3, 0, 0, 2, 2, 1, 0, 0]
else
[3, 0, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 3102 then
(if i.val < 3101 then
[3, 0, 0, 2, 2, 1, 3, 3]
else
[3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 3103 then
[3, 0, 0, 3, 2, 1, 0, 0]
else
[3, 0, 0, 3, 2, 1, 0, 3])))))
else
(if i.val < 3120 then
(if i.val < 3112 then
(if i.val < 3108 then
(if i.val < 3106 then
(if i.val < 3105 then
[3, 0, 0, 3, 2, 2, 1, 1]
else
[3, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 3107 then
[3, 0, 1, 1, 0, 2, 2, 1]
else
[3, 0, 1, 1, 0, 2, 2, 3]))
else
(if i.val < 3110 then
(if i.val < 3109 then
[3, 0, 1, 1, 0, 3, 2, 1]
else
[3, 0, 1, 1, 0, 3, 3, 0])
else
(if i.val < 3111 then
[3, 0, 1, 1, 0, 3, 3, 2]
else
[3, 0, 1, 1, 2, 2, 3, 0])))
else
(if i.val < 3116 then
(if i.val < 3114 then
(if i.val < 3113 then
[3, 0, 1, 1, 2, 2, 3, 3]
else
[3, 0, 1, 1, 2, 3, 3, 2])
else
(if i.val < 3115 then
[3, 0, 1, 2, 1, 1, 0, 3]
else
[3, 0, 1, 2, 1, 1, 3, 0]))
else
(if i.val < 3118 then
(if i.val < 3117 then
[3, 0, 1, 2, 2, 1, 0, 0]
else
[3, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 3119 then
[3, 0, 1, 2, 3, 3, 0, 0]
else
[3, 0, 1, 2, 3, 3, 0, 1]))))
else
(if i.val < 3128 then
(if i.val < 3124 then
(if i.val < 3122 then
(if i.val < 3121 then
[3, 0, 2, 1, 0, 3, 0, 0]
else
[3, 0, 2, 1, 0, 3, 3, 0])
else
(if i.val < 3123 then
[3, 0, 2, 1, 1, 0, 3, 3]
else
[3, 0, 2, 1, 1, 3, 2, 2]))
else
(if i.val < 3126 then
(if i.val < 3125 then
[3, 0, 2, 1, 3, 3, 0, 0]
else
[3, 0, 2, 2, 1, 0, 0, 3])
else
(if i.val < 3127 then
[3, 0, 2, 2, 1, 0, 3, 2]
else
[3, 0, 2, 2, 1, 1, 3, 2])))
else
(if i.val < 3132 then
(if i.val < 3130 then
(if i.val < 3129 then
[3, 0, 2, 2, 1, 1, 3, 3]
else
[3, 0, 2, 2, 3, 0, 1, 2])
else
(if i.val < 3131 then
[3, 0, 2, 3, 3, 0, 1, 2]
else
[3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 3134 then
(if i.val < 3133 then
[3, 2, 1, 0, 0, 1, 2, 3]
else
[3, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 3135 then
[3, 2, 1, 0, 3, 2, 2, 3]
else
[3, 2, 1, 1, 0, 0, 2, 1]))))))
else
(if i.val < 3168 then
(if i.val < 3152 then
(if i.val < 3144 then
(if i.val < 3140 then
(if i.val < 3138 then
(if i.val < 3137 then
[3, 2, 1, 1, 0, 3, 3, 0]
else
[3, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 3139 then
[3, 2, 2, 1, 0, 0, 3, 0]
else
[3, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3142 then
(if i.val < 3141 then
[3, 2, 2, 1, 0, 3, 3, 0]
else
[3, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 3143 then
[3, 2, 2, 1, 3, 0, 0, 1]
else
[3, 2, 2, 1, 3, 0, 2, 1])))
else
(if i.val < 3148 then
(if i.val < 3146 then
(if i.val < 3145 then
[3, 2, 2, 3, 0, 0, 1, 1]
else
[3, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 3147 then
[3, 3, 0, 0, 1, 2, 1, 3]
else
[3, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 3150 then
(if i.val < 3149 then
[3, 3, 0, 0, 1, 2, 3, 3]
else
[3, 3, 0, 0, 2, 1, 0, 0])
else
(if i.val < 3151 then
[3, 3, 0, 0, 2, 1, 1, 3]
else
[3, 3, 0, 0, 2, 3, 3, 2]))))
else
(if i.val < 3160 then
(if i.val < 3156 then
(if i.val < 3154 then
(if i.val < 3153 then
[3, 3, 0, 1, 1, 0, 2, 1]
else
[3, 3, 0, 1, 1, 0, 2, 2])
else
(if i.val < 3155 then
[3, 3, 0, 1, 1, 0, 3, 3]
else
[3, 3, 0, 1, 2, 1, 1, 3]))
else
(if i.val < 3158 then
(if i.val < 3157 then
[3, 3, 0, 1, 2, 3, 0, 0]
else
[3, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 3159 then
[3, 3, 0, 2, 1, 1, 0, 0]
else
[3, 3, 0, 2, 1, 1, 2, 3])))
else
(if i.val < 3164 then
(if i.val < 3162 then
(if i.val < 3161 then
[3, 3, 2, 1, 0, 0, 3, 3]
else
[3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 3163 then
[3, 3, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 0, 1, 2, 1, 1]))
else
(if i.val < 3166 then
(if i.val < 3165 then
[0, 0, 1, 0, 0, 1, 2, 1, 3]
else
[0, 0, 1, 0, 0, 1, 2, 2, 1])
else
(if i.val < 3167 then
[0, 0, 1, 0, 0, 1, 2, 2, 3]
else
[0, 0, 1, 0, 0, 1, 2, 3, 0])))))
else
(if i.val < 3184 then
(if i.val < 3176 then
(if i.val < 3172 then
(if i.val < 3170 then
(if i.val < 3169 then
[0, 0, 1, 0, 0, 1, 2, 3, 2]
else
[0, 0, 1, 0, 0, 1, 2, 3, 3])
else
(if i.val < 3171 then
[0, 0, 1, 0, 0, 1, 3, 0, 0]
else
[0, 0, 1, 0, 0, 1, 3, 0, 1]))
else
(if i.val < 3174 then
(if i.val < 3173 then
[0, 0, 1, 0, 0, 1, 3, 2, 1]
else
[0, 0, 1, 0, 0, 1, 3, 3, 0])
else
(if i.val < 3175 then
[0, 0, 1, 0, 0, 1, 3, 3, 2]
else
[0, 0, 1, 0, 0, 2, 1, 0, 3])))
else
(if i.val < 3180 then
(if i.val < 3178 then
(if i.val < 3177 then
[0, 0, 1, 0, 0, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 2, 1, 3, 0])
else
(if i.val < 3179 then
[0, 0, 1, 0, 0, 2, 1, 3, 3]
else
[0, 0, 1, 0, 0, 2, 2, 1, 3]))
else
(if i.val < 3182 then
(if i.val < 3181 then
[0, 0, 1, 0, 0, 2, 2, 3, 0]
else
[0, 0, 1, 0, 0, 2, 2, 3, 2])
else
(if i.val < 3183 then
[0, 0, 1, 0, 0, 2, 2, 3, 3]
else
[0, 0, 1, 0, 0, 2, 3, 0, 0]))))
else
(if i.val < 3192 then
(if i.val < 3188 then
(if i.val < 3186 then
(if i.val < 3185 then
[0, 0, 1, 0, 0, 2, 3, 0, 1]
else
[0, 0, 1, 0, 0, 2, 3, 2, 1])
else
(if i.val < 3187 then
[0, 0, 1, 0, 0, 2, 3, 3, 0]
else
[0, 0, 1, 0, 0, 2, 3, 3, 2]))
else
(if i.val < 3190 then
(if i.val < 3189 then
[0, 0, 1, 0, 0, 3, 0, 0, 1]
else
[0, 0, 1, 0, 0, 3, 0, 0, 3])
else
(if i.val < 3191 then
[0, 0, 1, 0, 0, 3, 0, 1, 2]
else
[0, 0, 1, 0, 0, 3, 0, 2, 1])))
else
(if i.val < 3196 then
(if i.val < 3194 then
(if i.val < 3193 then
[0, 0, 1, 0, 0, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 3, 2, 1, 1])
else
(if i.val < 3195 then
[0, 0, 1, 0, 0, 3, 2, 2, 1]
else
[0, 0, 1, 0, 0, 3, 2, 2, 3]))
else
(if i.val < 3198 then
(if i.val < 3197 then
[0, 0, 1, 0, 0, 3, 3, 0, 0]
else
[0, 0, 1, 0, 0, 3, 3, 0, 1])
else
(if i.val < 3199 then
[0, 0, 1, 0, 0, 3, 3, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 2, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0025 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3264 then
(if i.val < 3232 then
(if i.val < 3216 then
(if i.val < 3208 then
(if i.val < 3204 then
(if i.val < 3202 then
(if i.val < 3201 then
[0, 0, 1, 0, 2, 1, 0, 0, 3]
else
[0, 0, 1, 0, 2, 1, 0, 3, 0])
else
(if i.val < 3203 then
[0, 0, 1, 0, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 2, 1, 0, 3, 3]))
else
(if i.val < 3206 then
(if i.val < 3205 then
[0, 0, 1, 0, 2, 1, 1, 0, 0]
else
[0, 0, 1, 0, 2, 1, 1, 0, 3])
else
(if i.val < 3207 then
[0, 0, 1, 0, 2, 1, 1, 2, 3]
else
[0, 0, 1, 0, 2, 1, 1, 3, 2])))
else
(if i.val < 3212 then
(if i.val < 3210 then
(if i.val < 3209 then
[0, 0, 1, 0, 2, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 1, 3, 0, 1])
else
(if i.val < 3211 then
[0, 0, 1, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 0, 2, 2, 1, 0, 0]))
else
(if i.val < 3214 then
(if i.val < 3213 then
[0, 0, 1, 0, 2, 2, 1, 0, 3]
else
[0, 0, 1, 0, 2, 2, 1, 1, 3])
else
(if i.val < 3215 then
[0, 0, 1, 0, 2, 2, 1, 3, 0]
else
[0, 0, 1, 0, 2, 2, 1, 3, 2]))))
else
(if i.val < 3224 then
(if i.val < 3220 then
(if i.val < 3218 then
(if i.val < 3217 then
[0, 0, 1, 0, 2, 2, 1, 3, 3]
else
[0, 0, 1, 0, 2, 2, 3, 0, 0])
else
(if i.val < 3219 then
[0, 0, 1, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 0, 2, 2, 3, 2, 1]))
else
(if i.val < 3222 then
(if i.val < 3221 then
[0, 0, 1, 0, 2, 2, 3, 2, 2]
else
[0, 0, 1, 0, 2, 2, 3, 3, 2])
else
(if i.val < 3223 then
[0, 0, 1, 0, 2, 3, 0, 0, 3]
else
[0, 0, 1, 0, 2, 3, 0, 1, 2])))
else
(if i.val < 3228 then
(if i.val < 3226 then
(if i.val < 3225 then
[0, 0, 1, 0, 2, 3, 0, 2, 1]
else
[0, 0, 1, 0, 2, 3, 0, 2, 2])
else
(if i.val < 3227 then
[0, 0, 1, 0, 2, 3, 2, 1, 1]
else
[0, 0, 1, 0, 2, 3, 2, 2, 3]))
else
(if i.val < 3230 then
(if i.val < 3229 then
[0, 0, 1, 0, 2, 3, 3, 0, 0]
else
[0, 0, 1, 0, 2, 3, 3, 0, 1])
else
(if i.val < 3231 then
[0, 0, 1, 0, 3, 0, 0, 1, 1]
else
[0, 0, 1, 0, 3, 0, 0, 1, 3])))))
else
(if i.val < 3248 then
(if i.val < 3240 then
(if i.val < 3236 then
(if i.val < 3234 then
(if i.val < 3233 then
[0, 0, 1, 0, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 3, 0, 0, 2, 2])
else
(if i.val < 3235 then
[0, 0, 1, 0, 3, 0, 0, 3, 2]
else
[0, 0, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 3238 then
(if i.val < 3237 then
[0, 0, 1, 0, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 3, 0, 1, 2, 3])
else
(if i.val < 3239 then
[0, 0, 1, 0, 3, 0, 2, 1, 1]
else
[0, 0, 1, 0, 3, 0, 2, 1, 3])))
else
(if i.val < 3244 then
(if i.val < 3242 then
(if i.val < 3241 then
[0, 0, 1, 0, 3, 0, 2, 2, 1]
else
[0, 0, 1, 0, 3, 0, 2, 2, 3])
else
(if i.val < 3243 then
[0, 0, 1, 0, 3, 2, 1, 0, 0]
else
[0, 0, 1, 0, 3, 2, 1, 0, 3]))
else
(if i.val < 3246 then
(if i.val < 3245 then
[0, 0, 1, 0, 3, 2, 2, 1, 1]
else
[0, 0, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 3247 then
[0, 0, 1, 0, 3, 2, 2, 3, 0]
else
[0, 0, 1, 0, 3, 3, 0, 1, 2]))))
else
(if i.val < 3256 then
(if i.val < 3252 then
(if i.val < 3250 then
(if i.val < 3249 then
[0, 0, 1, 0, 3, 3, 0, 2, 1]
else
[0, 0, 1, 0, 3, 3, 0, 2, 2])
else
(if i.val < 3251 then
[0, 0, 1, 0, 3, 3, 0, 2, 3]
else
[0, 0, 1, 0, 3, 3, 2, 1, 1]))
else
(if i.val < 3254 then
(if i.val < 3253 then
[0, 0, 1, 0, 3, 3, 2, 2, 1]
else
[0, 0, 1, 1, 0, 0, 2, 1, 1])
else
(if i.val < 3255 then
[0, 0, 1, 1, 0, 0, 2, 1, 3]
else
[0, 0, 1, 1, 0, 0, 2, 2, 1])))
else
(if i.val < 3260 then
(if i.val < 3258 then
(if i.val < 3257 then
[0, 0, 1, 1, 0, 0, 2, 2, 3]
else
[0, 0, 1, 1, 0, 0, 2, 3, 2])
else
(if i.val < 3259 then
[0, 0, 1, 1, 0, 0, 3, 0, 0]
else
[0, 0, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 3262 then
(if i.val < 3261 then
[0, 0, 1, 1, 0, 0, 3, 2, 1]
else
[0, 0, 1, 1, 0, 0, 3, 2, 2])
else
(if i.val < 3263 then
[0, 0, 1, 1, 0, 0, 3, 3, 0]
else
[0, 0, 1, 1, 0, 0, 3, 3, 2]))))))
else
(if i.val < 3296 then
(if i.val < 3280 then
(if i.val < 3272 then
(if i.val < 3268 then
(if i.val < 3266 then
(if i.val < 3265 then
[0, 0, 1, 1, 0, 2, 1, 0, 3]
else
[0, 0, 1, 1, 0, 2, 1, 1, 3])
else
(if i.val < 3267 then
[0, 0, 1, 1, 0, 2, 1, 3, 0]
else
[0, 0, 1, 1, 0, 2, 1, 3, 2]))
else
(if i.val < 3270 then
(if i.val < 3269 then
[0, 0, 1, 1, 0, 2, 1, 3, 3]
else
[0, 0, 1, 1, 0, 2, 2, 1, 3])
else
(if i.val < 3271 then
[0, 0, 1, 1, 0, 2, 2, 3, 0]
else
[0, 0, 1, 1, 0, 2, 2, 3, 2])))
else
(if i.val < 3276 then
(if i.val < 3274 then
(if i.val < 3273 then
[0, 0, 1, 1, 0, 2, 2, 3, 3]
else
[0, 0, 1, 1, 0, 2, 3, 0, 1])
else
(if i.val < 3275 then
[0, 0, 1, 1, 0, 2, 3, 2, 1]
else
[0, 0, 1, 1, 0, 2, 3, 3, 2]))
else
(if i.val < 3278 then
(if i.val < 3277 then
[0, 0, 1, 1, 0, 3, 0, 0, 3]
else
[0, 0, 1, 1, 0, 3, 0, 1, 2])
else
(if i.val < 3279 then
[0, 0, 1, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 1, 0, 3, 0, 2, 2]))))
else
(if i.val < 3288 then
(if i.val < 3284 then
(if i.val < 3282 then
(if i.val < 3281 then
[0, 0, 1, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 1, 0, 3, 2, 2, 1])
else
(if i.val < 3283 then
[0, 0, 1, 1, 0, 3, 2, 2, 3]
else
[0, 0, 1, 1, 0, 3, 3, 0, 1]))
else
(if i.val < 3286 then
(if i.val < 3285 then
[0, 0, 1, 1, 0, 3, 3, 2, 2]
else
[0, 0, 1, 1, 2, 1, 0, 0, 3])
else
(if i.val < 3287 then
[0, 0, 1, 1, 2, 1, 0, 3, 0]
else
[0, 0, 1, 1, 2, 1, 0, 3, 2])))
else
(if i.val < 3292 then
(if i.val < 3290 then
(if i.val < 3289 then
[0, 0, 1, 1, 2, 1, 0, 3, 3]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3])
else
(if i.val < 3291 then
[0, 0, 1, 1, 2, 1, 1, 2, 3]
else
[0, 0, 1, 1, 2, 1, 1, 3, 0]))
else
(if i.val < 3294 then
(if i.val < 3293 then
[0, 0, 1, 1, 2, 1, 1, 3, 2]
else
[0, 0, 1, 1, 2, 1, 1, 3, 3])
else
(if i.val < 3295 then
[0, 0, 1, 1, 2, 1, 3, 0, 0]
else
[0, 0, 1, 1, 2, 1, 3, 0, 1])))))
else
(if i.val < 3312 then
(if i.val < 3304 then
(if i.val < 3300 then
(if i.val < 3298 then
(if i.val < 3297 then
[0, 0, 1, 1, 2, 1, 3, 2, 1]
else
[0, 0, 1, 1, 2, 1, 3, 3, 2])
else
(if i.val < 3299 then
[0, 0, 1, 1, 2, 2, 1, 0, 0]
else
[0, 0, 1, 1, 2, 2, 1, 0, 3]))
else
(if i.val < 3302 then
(if i.val < 3301 then
[0, 0, 1, 1, 2, 2, 1, 1, 3]
else
[0, 0, 1, 1, 2, 2, 1, 3, 0])
else
(if i.val < 3303 then
[0, 0, 1, 1, 2, 2, 1, 3, 2]
else
[0, 0, 1, 1, 2, 2, 1, 3, 3])))
else
(if i.val < 3308 then
(if i.val < 3306 then
(if i.val < 3305 then
[0, 0, 1, 1, 2, 2, 3, 0, 0]
else
[0, 0, 1, 1, 2, 2, 3, 0, 1])
else
(if i.val < 3307 then
[0, 0, 1, 1, 2, 2, 3, 2, 1]
else
[0, 0, 1, 1, 2, 2, 3, 2, 2]))
else
(if i.val < 3310 then
(if i.val < 3309 then
[0, 0, 1, 1, 2, 2, 3, 3, 2]
else
[0, 0, 1, 1, 2, 3, 0, 0, 3])
else
(if i.val < 3311 then
[0, 0, 1, 1, 2, 3, 0, 1, 2]
else
[0, 0, 1, 1, 2, 3, 0, 2, 1]))))
else
(if i.val < 3320 then
(if i.val < 3316 then
(if i.val < 3314 then
(if i.val < 3313 then
[0, 0, 1, 1, 2, 3, 0, 2, 2]
else
[0, 0, 1, 1, 2, 3, 2, 1, 1])
else
(if i.val < 3315 then
[0, 0, 1, 1, 2, 3, 2, 2, 3]
else
[0, 0, 1, 1, 2, 3, 3, 0, 0]))
else
(if i.val < 3318 then
(if i.val < 3317 then
[0, 0, 1, 1, 2, 3, 3, 0, 1]
else
[0, 0, 1, 1, 2, 3, 3, 2, 1])
else
(if i.val < 3319 then
[0, 0, 1, 1, 3, 0, 0, 1, 1]
else
[0, 0, 1, 1, 3, 0, 0, 2, 1])))
else
(if i.val < 3324 then
(if i.val < 3322 then
(if i.val < 3321 then
[0, 0, 1, 1, 3, 0, 0, 2, 2]
else
[0, 0, 1, 1, 3, 0, 0, 3, 2])
else
(if i.val < 3323 then
[0, 0, 1, 1, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 3, 0, 1, 2, 2]))
else
(if i.val < 3326 then
(if i.val < 3325 then
[0, 0, 1, 1, 3, 0, 1, 2, 3]
else
[0, 0, 1, 1, 3, 0, 2, 1, 1])
else
(if i.val < 3327 then
[0, 0, 1, 1, 3, 0, 2, 1, 3]
else
[0, 0, 1, 1, 3, 0, 2, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0026 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3392 then
(if i.val < 3360 then
(if i.val < 3344 then
(if i.val < 3336 then
(if i.val < 3332 then
(if i.val < 3330 then
(if i.val < 3329 then
[0, 0, 1, 1, 3, 0, 2, 2, 3]
else
[0, 0, 1, 1, 3, 2, 1, 0, 0])
else
(if i.val < 3331 then
[0, 0, 1, 1, 3, 2, 1, 0, 3]
else
[0, 0, 1, 1, 3, 2, 2, 3, 0]))
else
(if i.val < 3334 then
(if i.val < 3333 then
[0, 0, 1, 1, 3, 3, 0, 1, 2]
else
[0, 0, 1, 1, 3, 3, 0, 2, 1])
else
(if i.val < 3335 then
[0, 0, 1, 1, 3, 3, 0, 2, 2]
else
[0, 0, 1, 1, 3, 3, 2, 1, 1])))
else
(if i.val < 3340 then
(if i.val < 3338 then
(if i.val < 3337 then
[0, 0, 1, 1, 3, 3, 2, 2, 1]
else
[0, 0, 1, 2, 1, 0, 0, 1, 3])
else
(if i.val < 3339 then
[0, 0, 1, 2, 1, 0, 0, 3, 0]
else
[0, 0, 1, 2, 1, 0, 0, 3, 2]))
else
(if i.val < 3342 then
(if i.val < 3341 then
[0, 0, 1, 2, 1, 0, 0, 3, 3]
else
[0, 0, 1, 2, 1, 0, 3, 0, 0])
else
(if i.val < 3343 then
[0, 0, 1, 2, 1, 0, 3, 0, 1]
else
[0, 0, 1, 2, 1, 0, 3, 2, 1]))))
else
(if i.val < 3352 then
(if i.val < 3348 then
(if i.val < 3346 then
(if i.val < 3345 then
[0, 0, 1, 2, 1, 0, 3, 3, 0]
else
[0, 0, 1, 2, 1, 0, 3, 3, 2])
else
(if i.val < 3347 then
[0, 0, 1, 2, 1, 1, 0, 0, 3]
else
[0, 0, 1, 2, 1, 1, 0, 3, 3]))
else
(if i.val < 3350 then
(if i.val < 3349 then
[0, 0, 1, 2, 1, 1, 2, 3, 2]
else
[0, 0, 1, 2, 1, 1, 2, 3, 3])
else
(if i.val < 3351 then
[0, 0, 1, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 2, 1, 1, 3, 0, 1])))
else
(if i.val < 3356 then
(if i.val < 3354 then
(if i.val < 3353 then
[0, 0, 1, 2, 1, 1, 3, 2, 2]
else
[0, 0, 1, 2, 1, 1, 3, 3, 2])
else
(if i.val < 3355 then
[0, 0, 1, 2, 1, 3, 0, 0, 1]
else
[0, 0, 1, 2, 1, 3, 0, 0, 3]))
else
(if i.val < 3358 then
(if i.val < 3357 then
[0, 0, 1, 2, 1, 3, 0, 1, 2]
else
[0, 0, 1, 2, 1, 3, 0, 2, 1])
else
(if i.val < 3359 then
[0, 0, 1, 2, 1, 3, 0, 2, 2]
else
[0, 0, 1, 2, 1, 3, 0, 2, 3])))))
else
(if i.val < 3376 then
(if i.val < 3368 then
(if i.val < 3364 then
(if i.val < 3362 then
(if i.val < 3361 then
[0, 0, 1, 2, 1, 3, 2, 1, 1]
else
[0, 0, 1, 2, 1, 3, 2, 2, 1])
else
(if i.val < 3363 then
[0, 0, 1, 2, 1, 3, 2, 2, 3]
else
[0, 0, 1, 2, 1, 3, 3, 0, 0]))
else
(if i.val < 3366 then
(if i.val < 3365 then
[0, 0, 1, 2, 1, 3, 3, 0, 1]
else
[0, 0, 1, 2, 1, 3, 3, 2, 1])
else
(if i.val < 3367 then
[0, 0, 1, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0])))
else
(if i.val < 3372 then
(if i.val < 3370 then
(if i.val < 3369 then
[0, 0, 1, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 2, 2, 1, 0, 3, 3])
else
(if i.val < 3371 then
[0, 0, 1, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 2, 2, 1, 1, 3, 3]))
else
(if i.val < 3374 then
(if i.val < 3373 then
[0, 0, 1, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 2, 2, 1, 3, 0, 1])
else
(if i.val < 3375 then
[0, 0, 1, 2, 2, 1, 3, 3, 2]
else
[0, 0, 1, 2, 2, 3, 0, 0, 3]))))
else
(if i.val < 3384 then
(if i.val < 3380 then
(if i.val < 3378 then
(if i.val < 3377 then
[0, 0, 1, 2, 2, 3, 0, 1, 2]
else
[0, 0, 1, 2, 2, 3, 0, 2, 3])
else
(if i.val < 3379 then
[0, 0, 1, 2, 2, 3, 2, 1, 1]
else
[0, 0, 1, 2, 2, 3, 2, 2, 1]))
else
(if i.val < 3382 then
(if i.val < 3381 then
[0, 0, 1, 2, 2, 3, 2, 2, 3]
else
[0, 0, 1, 2, 2, 3, 3, 0, 0])
else
(if i.val < 3383 then
[0, 0, 1, 2, 2, 3, 3, 2, 1]
else
[0, 0, 1, 2, 2, 3, 3, 2, 2])))
else
(if i.val < 3388 then
(if i.val < 3386 then
(if i.val < 3385 then
[0, 0, 1, 2, 3, 0, 0, 1, 1]
else
[0, 0, 1, 2, 3, 0, 0, 1, 3])
else
(if i.val < 3387 then
[0, 0, 1, 2, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 3, 0, 0, 2, 2]))
else
(if i.val < 3390 then
(if i.val < 3389 then
[0, 0, 1, 2, 3, 0, 0, 2, 3]
else
[0, 0, 1, 2, 3, 0, 0, 3, 2])
else
(if i.val < 3391 then
[0, 0, 1, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2]))))))
else
(if i.val < 3424 then
(if i.val < 3408 then
(if i.val < 3400 then
(if i.val < 3396 then
(if i.val < 3394 then
(if i.val < 3393 then
[0, 0, 1, 2, 3, 0, 1, 2, 3]
else
[0, 0, 1, 2, 3, 0, 2, 1, 1])
else
(if i.val < 3395 then
[0, 0, 1, 2, 3, 0, 2, 1, 3]
else
[0, 0, 1, 2, 3, 0, 2, 2, 1]))
else
(if i.val < 3398 then
(if i.val < 3397 then
[0, 0, 1, 2, 3, 0, 2, 2, 3]
else
[0, 0, 1, 2, 3, 2, 1, 0, 0])
else
(if i.val < 3399 then
[0, 0, 1, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 3, 2, 2, 1, 1])))
else
(if i.val < 3404 then
(if i.val < 3402 then
(if i.val < 3401 then
[0, 0, 1, 2, 3, 2, 2, 3, 0]
else
[0, 0, 1, 2, 3, 3, 0, 0, 1])
else
(if i.val < 3403 then
[0, 0, 1, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 2, 3, 3, 0, 2, 1]))
else
(if i.val < 3406 then
(if i.val < 3405 then
[0, 0, 1, 2, 3, 3, 0, 2, 2]
else
[0, 0, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 3407 then
[0, 0, 1, 2, 3, 3, 2, 2, 1]
else
[0, 0, 1, 3, 0, 0, 1, 1, 3]))))
else
(if i.val < 3416 then
(if i.val < 3412 then
(if i.val < 3410 then
(if i.val < 3409 then
[0, 0, 1, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 3, 0, 0, 1, 2, 3])
else
(if i.val < 3411 then
[0, 0, 1, 3, 0, 0, 2, 1, 1]
else
[0, 0, 1, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 3414 then
(if i.val < 3413 then
[0, 0, 1, 3, 0, 0, 2, 2, 3]
else
[0, 0, 1, 3, 0, 0, 2, 3, 3])
else
(if i.val < 3415 then
[0, 0, 1, 3, 0, 0, 3, 2, 1]
else
[0, 0, 1, 3, 0, 0, 3, 2, 2])))
else
(if i.val < 3420 then
(if i.val < 3418 then
(if i.val < 3417 then
[0, 0, 1, 3, 0, 1, 1, 0, 3]
else
[0, 0, 1, 3, 0, 1, 1, 2, 1])
else
(if i.val < 3419 then
[0, 0, 1, 3, 0, 1, 1, 2, 2]
else
[0, 0, 1, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 3422 then
(if i.val < 3421 then
[0, 0, 1, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 3, 0, 1, 2, 3, 0])
else
(if i.val < 3423 then
[0, 0, 1, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 3, 0, 2, 1, 0, 3])))))
else
(if i.val < 3440 then
(if i.val < 3432 then
(if i.val < 3428 then
(if i.val < 3426 then
(if i.val < 3425 then
[0, 0, 1, 3, 0, 2, 1, 1, 3]
else
[0, 0, 1, 3, 0, 2, 1, 3, 2])
else
(if i.val < 3427 then
[0, 0, 1, 3, 0, 2, 1, 3, 3]
else
[0, 0, 1, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 3430 then
(if i.val < 3429 then
[0, 0, 1, 3, 0, 2, 2, 3, 0]
else
[0, 0, 1, 3, 0, 2, 2, 3, 3])
else
(if i.val < 3431 then
[0, 0, 1, 3, 0, 2, 3, 3, 2]
else
[0, 0, 1, 3, 2, 1, 0, 0, 3])))
else
(if i.val < 3436 then
(if i.val < 3434 then
(if i.val < 3433 then
[0, 0, 1, 3, 2, 1, 1, 0, 0]
else
[0, 0, 1, 3, 2, 2, 1, 0, 0])
else
(if i.val < 3435 then
[0, 0, 1, 3, 2, 2, 1, 0, 3]
else
[0, 0, 1, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 3438 then
(if i.val < 3437 then
[0, 0, 1, 3, 2, 2, 1, 3, 2]
else
[0, 0, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 3439 then
[0, 0, 1, 3, 2, 2, 3, 0, 1]
else
[0, 0, 1, 3, 3, 0, 0, 1, 1]))))
else
(if i.val < 3448 then
(if i.val < 3444 then
(if i.val < 3442 then
(if i.val < 3441 then
[0, 0, 1, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 3, 3, 0, 0, 2, 3])
else
(if i.val < 3443 then
[0, 0, 1, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 3, 3, 0, 1, 2, 2]))
else
(if i.val < 3446 then
(if i.val < 3445 then
[0, 0, 1, 3, 3, 0, 1, 2, 3]
else
[0, 0, 1, 3, 3, 0, 2, 1, 3])
else
(if i.val < 3447 then
[0, 0, 1, 3, 3, 0, 2, 2, 3]
else
[0, 0, 1, 3, 3, 0, 2, 3, 3])))
else
(if i.val < 3452 then
(if i.val < 3450 then
(if i.val < 3449 then
[0, 0, 1, 3, 3, 2, 1, 0, 0]
else
[0, 0, 1, 3, 3, 2, 1, 0, 3])
else
(if i.val < 3451 then
[0, 0, 1, 3, 3, 2, 2, 1, 1]
else
[0, 0, 2, 1, 0, 0, 1, 2, 2]))
else
(if i.val < 3454 then
(if i.val < 3453 then
[0, 0, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 2, 1, 0, 0, 1, 3, 3])
else
(if i.val < 3455 then
[0, 0, 2, 1, 0, 0, 3, 0, 0]
else
[0, 0, 2, 1, 0, 0, 3, 0, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0027 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3520 then
(if i.val < 3488 then
(if i.val < 3472 then
(if i.val < 3464 then
(if i.val < 3460 then
(if i.val < 3458 then
(if i.val < 3457 then
[0, 0, 2, 1, 0, 0, 3, 2, 2]
else
[0, 0, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 3459 then
[0, 0, 2, 1, 0, 3, 0, 0, 1]
else
[0, 0, 2, 1, 0, 3, 0, 0, 3]))
else
(if i.val < 3462 then
(if i.val < 3461 then
[0, 0, 2, 1, 0, 3, 0, 1, 2]
else
[0, 0, 2, 1, 0, 3, 0, 2, 1])
else
(if i.val < 3463 then
[0, 0, 2, 1, 0, 3, 0, 2, 2]
else
[0, 0, 2, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 3468 then
(if i.val < 3466 then
(if i.val < 3465 then
[0, 0, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 3467 then
[0, 0, 2, 1, 1, 0, 0, 3, 0]
else
[0, 0, 2, 1, 1, 0, 0, 3, 2]))
else
(if i.val < 3470 then
(if i.val < 3469 then
[0, 0, 2, 1, 1, 0, 0, 3, 3]
else
[0, 0, 2, 1, 1, 0, 2, 1, 3])
else
(if i.val < 3471 then
[0, 0, 2, 1, 1, 0, 2, 3, 2]
else
[0, 0, 2, 1, 1, 0, 3, 0, 0]))))
else
(if i.val < 3480 then
(if i.val < 3476 then
(if i.val < 3474 then
(if i.val < 3473 then
[0, 0, 2, 1, 1, 0, 3, 0, 1]
else
[0, 0, 2, 1, 1, 0, 3, 2, 1])
else
(if i.val < 3475 then
[0, 0, 2, 1, 1, 0, 3, 3, 0]
else
[0, 0, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 3478 then
(if i.val < 3477 then
[0, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 0, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 3479 then
[0, 0, 2, 1, 1, 2, 3, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 1, 2])))
else
(if i.val < 3484 then
(if i.val < 3482 then
(if i.val < 3481 then
[0, 0, 2, 1, 1, 3, 0, 2, 2]
else
[0, 0, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 3483 then
[0, 0, 2, 1, 1, 3, 2, 2, 1]
else
[0, 0, 2, 1, 1, 3, 2, 2, 3]))
else
(if i.val < 3486 then
(if i.val < 3485 then
[0, 0, 2, 1, 1, 3, 3, 0, 1]
else
[0, 0, 2, 1, 1, 3, 3, 2, 2])
else
(if i.val < 3487 then
[0, 0, 2, 1, 3, 0, 0, 2, 1]
else
[0, 0, 2, 1, 3, 0, 0, 2, 2])))))
else
(if i.val < 3504 then
(if i.val < 3496 then
(if i.val < 3492 then
(if i.val < 3490 then
(if i.val < 3489 then
[0, 0, 2, 1, 3, 0, 0, 2, 3]
else
[0, 0, 2, 1, 3, 0, 0, 3, 2])
else
(if i.val < 3491 then
[0, 0, 2, 1, 3, 0, 1, 2, 1]
else
[0, 0, 2, 1, 3, 0, 1, 2, 2]))
else
(if i.val < 3494 then
(if i.val < 3493 then
[0, 0, 2, 1, 3, 0, 1, 2, 3]
else
[0, 0, 2, 1, 3, 0, 2, 2, 3])
else
(if i.val < 3495 then
[0, 0, 2, 1, 3, 2, 1, 0, 0]
else
[0, 0, 2, 1, 3, 2, 1, 0, 3])))
else
(if i.val < 3500 then
(if i.val < 3498 then
(if i.val < 3497 then
[0, 0, 2, 1, 3, 2, 2, 1, 1]
else
[0, 0, 2, 1, 3, 2, 2, 1, 3])
else
(if i.val < 3499 then
[0, 0, 2, 1, 3, 3, 0, 0, 1]
else
[0, 0, 2, 1, 3, 3, 0, 1, 2]))
else
(if i.val < 3502 then
(if i.val < 3501 then
[0, 0, 2, 1, 3, 3, 0, 2, 3]
else
[0, 0, 2, 1, 3, 3, 2, 1, 1])
else
(if i.val < 3503 then
[0, 0, 2, 1, 3, 3, 2, 2, 1]
else
[0, 0, 2, 2, 1, 0, 0, 3, 0]))))
else
(if i.val < 3512 then
(if i.val < 3508 then
(if i.val < 3506 then
(if i.val < 3505 then
[0, 0, 2, 2, 1, 0, 0, 3, 2]
else
[0, 0, 2, 2, 1, 0, 0, 3, 3])
else
(if i.val < 3507 then
[0, 0, 2, 2, 1, 0, 3, 0, 1]
else
[0, 0, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3510 then
(if i.val < 3509 then
[0, 0, 2, 2, 1, 0, 3, 3, 0]
else
[0, 0, 2, 2, 1, 0, 3, 3, 2])
else
(if i.val < 3511 then
[0, 0, 2, 2, 1, 1, 0, 3, 2]
else
[0, 0, 2, 2, 1, 1, 3, 0, 0])))
else
(if i.val < 3516 then
(if i.val < 3514 then
(if i.val < 3513 then
[0, 0, 2, 2, 1, 1, 3, 0, 1]
else
[0, 0, 2, 2, 1, 1, 3, 2, 2])
else
(if i.val < 3515 then
[0, 0, 2, 2, 1, 1, 3, 3, 2]
else
[0, 0, 2, 2, 1, 3, 0, 0, 1]))
else
(if i.val < 3518 then
(if i.val < 3517 then
[0, 0, 2, 2, 1, 3, 0, 1, 2]
else
[0, 0, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 3519 then
[0, 0, 2, 2, 1, 3, 0, 2, 3]
else
[0, 0, 2, 2, 1, 3, 2, 1, 1]))))))
else
(if i.val < 3552 then
(if i.val < 3536 then
(if i.val < 3528 then
(if i.val < 3524 then
(if i.val < 3522 then
(if i.val < 3521 then
[0, 0, 2, 2, 1, 3, 2, 2, 1]
else
[0, 0, 2, 2, 1, 3, 2, 2, 3])
else
(if i.val < 3523 then
[0, 0, 2, 2, 1, 3, 3, 0, 0]
else
[0, 0, 2, 2, 1, 3, 3, 0, 1]))
else
(if i.val < 3526 then
(if i.val < 3525 then
[0, 0, 2, 2, 1, 3, 3, 2, 1]
else
[0, 0, 2, 2, 3, 0, 0, 1, 1])
else
(if i.val < 3527 then
[0, 0, 2, 2, 3, 0, 0, 2, 1]
else
[0, 0, 2, 2, 3, 0, 0, 2, 2])))
else
(if i.val < 3532 then
(if i.val < 3530 then
(if i.val < 3529 then
[0, 0, 2, 2, 3, 0, 0, 2, 3]
else
[0, 0, 2, 2, 3, 0, 1, 2, 1])
else
(if i.val < 3531 then
[0, 0, 2, 2, 3, 0, 1, 2, 2]
else
[0, 0, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 3534 then
(if i.val < 3533 then
[0, 0, 2, 2, 3, 0, 2, 1, 1]
else
[0, 0, 2, 2, 3, 0, 2, 1, 3])
else
(if i.val < 3535 then
[0, 0, 2, 2, 3, 0, 2, 2, 3]
else
[0, 0, 2, 2, 3, 0, 2, 3, 3]))))
else
(if i.val < 3544 then
(if i.val < 3540 then
(if i.val < 3538 then
(if i.val < 3537 then
[0, 0, 2, 2, 3, 2, 1, 0, 0]
else
[0, 0, 2, 2, 3, 2, 1, 0, 3])
else
(if i.val < 3539 then
[0, 0, 2, 2, 3, 2, 2, 1, 1]
else
[0, 0, 2, 2, 3, 2, 2, 1, 3]))
else
(if i.val < 3542 then
(if i.val < 3541 then
[0, 0, 2, 2, 3, 3, 0, 1, 2]
else
[0, 0, 2, 2, 3, 3, 0, 2, 3])
else
(if i.val < 3543 then
[0, 0, 2, 2, 3, 3, 2, 1, 1]
else
[0, 0, 2, 2, 3, 3, 2, 2, 1])))
else
(if i.val < 3548 then
(if i.val < 3546 then
(if i.val < 3545 then
[0, 0, 2, 3, 0, 0, 1, 1, 3]
else
[0, 0, 2, 3, 0, 0, 1, 2, 1])
else
(if i.val < 3547 then
[0, 0, 2, 3, 0, 0, 1, 2, 3]
else
[0, 0, 2, 3, 0, 0, 1, 3, 2]))
else
(if i.val < 3550 then
(if i.val < 3549 then
[0, 0, 2, 3, 0, 0, 2, 1, 1]
else
[0, 0, 2, 3, 0, 0, 2, 2, 1])
else
(if i.val < 3551 then
[0, 0, 2, 3, 0, 0, 2, 2, 3]
else
[0, 0, 2, 3, 0, 0, 2, 3, 2])))))
else
(if i.val < 3568 then
(if i.val < 3560 then
(if i.val < 3556 then
(if i.val < 3554 then
(if i.val < 3553 then
[0, 0, 2, 3, 0, 0, 2, 3, 3]
else
[0, 0, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 3555 then
[0, 0, 2, 3, 0, 1, 1, 0, 3]
else
[0, 0, 2, 3, 0, 1, 1, 2, 1]))
else
(if i.val < 3558 then
(if i.val < 3557 then
[0, 0, 2, 3, 0, 1, 1, 2, 2]
else
[0, 0, 2, 3, 0, 1, 2, 1, 1])
else
(if i.val < 3559 then
[0, 0, 2, 3, 0, 1, 2, 2, 1]
else
[0, 0, 2, 3, 0, 1, 2, 3, 3])))
else
(if i.val < 3564 then
(if i.val < 3562 then
(if i.val < 3561 then
[0, 0, 2, 3, 0, 2, 1, 0, 3]
else
[0, 0, 2, 3, 0, 2, 1, 1, 3])
else
(if i.val < 3563 then
[0, 0, 2, 3, 0, 2, 1, 3, 2]
else
[0, 0, 2, 3, 0, 2, 2, 1, 3]))
else
(if i.val < 3566 then
(if i.val < 3565 then
[0, 0, 2, 3, 0, 2, 2, 3, 0]
else
[0, 0, 2, 3, 0, 2, 2, 3, 3])
else
(if i.val < 3567 then
[0, 0, 2, 3, 0, 2, 3, 3, 0]
else
[0, 0, 2, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 3576 then
(if i.val < 3572 then
(if i.val < 3570 then
(if i.val < 3569 then
[0, 0, 2, 3, 2, 1, 0, 0, 3]
else
[0, 0, 2, 3, 2, 1, 0, 3, 2])
else
(if i.val < 3571 then
[0, 0, 2, 3, 2, 1, 0, 3, 3]
else
[0, 0, 2, 3, 2, 1, 1, 0, 3]))
else
(if i.val < 3574 then
(if i.val < 3573 then
[0, 0, 2, 3, 2, 1, 1, 2, 3]
else
[0, 0, 2, 3, 2, 2, 1, 0, 3])
else
(if i.val < 3575 then
[0, 0, 2, 3, 2, 2, 1, 1, 3]
else
[0, 0, 2, 3, 2, 2, 1, 3, 2])))
else
(if i.val < 3580 then
(if i.val < 3578 then
(if i.val < 3577 then
[0, 0, 2, 3, 2, 2, 3, 0, 0]
else
[0, 0, 2, 3, 2, 2, 3, 0, 1])
else
(if i.val < 3579 then
[0, 0, 2, 3, 3, 0, 0, 1, 1]
else
[0, 0, 2, 3, 3, 0, 0, 2, 1]))
else
(if i.val < 3582 then
(if i.val < 3581 then
[0, 0, 2, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 3, 3, 0, 1, 2, 1])
else
(if i.val < 3583 then
[0, 0, 2, 3, 3, 0, 1, 2, 2]
else
[0, 0, 2, 3, 3, 0, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0028 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3648 then
(if i.val < 3616 then
(if i.val < 3600 then
(if i.val < 3592 then
(if i.val < 3588 then
(if i.val < 3586 then
(if i.val < 3585 then
[0, 0, 2, 3, 3, 0, 2, 1, 3]
else
[0, 0, 2, 3, 3, 0, 2, 2, 1])
else
(if i.val < 3587 then
[0, 0, 2, 3, 3, 0, 2, 2, 3]
else
[0, 0, 2, 3, 3, 0, 2, 3, 3]))
else
(if i.val < 3590 then
(if i.val < 3589 then
[0, 0, 2, 3, 3, 2, 1, 0, 0]
else
[0, 0, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 3591 then
[0, 0, 2, 3, 3, 2, 2, 1, 1]
else
[0, 0, 3, 0, 0, 1, 1, 2, 1])))
else
(if i.val < 3596 then
(if i.val < 3594 then
(if i.val < 3593 then
[0, 0, 3, 0, 0, 1, 1, 2, 2]
else
[0, 0, 3, 0, 0, 1, 2, 1, 1])
else
(if i.val < 3595 then
[0, 0, 3, 0, 0, 1, 2, 1, 3]
else
[0, 0, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 3598 then
(if i.val < 3597 then
[0, 0, 3, 0, 0, 1, 2, 3, 2]
else
[0, 0, 3, 0, 0, 1, 2, 3, 3])
else
(if i.val < 3599 then
[0, 0, 3, 0, 0, 1, 3, 0, 0]
else
[0, 0, 3, 0, 0, 1, 3, 2, 1]))))
else
(if i.val < 3608 then
(if i.val < 3604 then
(if i.val < 3602 then
(if i.val < 3601 then
[0, 0, 3, 0, 0, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 2, 1, 1, 3])
else
(if i.val < 3603 then
[0, 0, 3, 0, 0, 2, 2, 1, 1]
else
[0, 0, 3, 0, 0, 2, 2, 3, 0]))
else
(if i.val < 3606 then
(if i.val < 3605 then
[0, 0, 3, 0, 0, 2, 2, 3, 2]
else
[0, 0, 3, 0, 0, 2, 3, 2, 1])
else
(if i.val < 3607 then
[0, 0, 3, 0, 0, 2, 3, 3, 2]
else
[0, 0, 3, 0, 0, 3, 2, 1, 1])))
else
(if i.val < 3612 then
(if i.val < 3610 then
(if i.val < 3609 then
[0, 0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 0, 3, 0, 0, 3, 2, 2, 3])
else
(if i.val < 3611 then
[0, 0, 3, 0, 1, 1, 0, 2, 1]
else
[0, 0, 3, 0, 1, 1, 0, 2, 2]))
else
(if i.val < 3614 then
(if i.val < 3613 then
[0, 0, 3, 0, 1, 1, 0, 3, 2]
else
[0, 0, 3, 0, 1, 1, 0, 3, 3])
else
(if i.val < 3615 then
[0, 0, 3, 0, 1, 1, 2, 1, 1]
else
[0, 0, 3, 0, 1, 1, 2, 2, 1])))))
else
(if i.val < 3632 then
(if i.val < 3624 then
(if i.val < 3620 then
(if i.val < 3618 then
(if i.val < 3617 then
[0, 0, 3, 0, 1, 1, 2, 3, 3]
else
[0, 0, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 3619 then
[0, 0, 3, 0, 1, 2, 2, 1, 3]
else
[0, 0, 3, 0, 1, 2, 2, 3, 0]))
else
(if i.val < 3622 then
(if i.val < 3621 then
[0, 0, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 3623 then
[0, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 3, 0, 2, 1, 0, 3, 2])))
else
(if i.val < 3628 then
(if i.val < 3626 then
(if i.val < 3625 then
[0, 0, 3, 0, 2, 1, 1, 0, 0]
else
[0, 0, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 3627 then
[0, 0, 3, 0, 2, 1, 1, 2, 3]
else
[0, 0, 3, 0, 2, 1, 3, 3, 2]))
else
(if i.val < 3630 then
(if i.val < 3629 then
[0, 0, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 3631 then
[0, 0, 3, 0, 2, 2, 1, 3, 2]
else
[0, 0, 3, 0, 2, 2, 3, 0, 1]))))
else
(if i.val < 3640 then
(if i.val < 3636 then
(if i.val < 3634 then
(if i.val < 3633 then
[0, 0, 3, 0, 2, 3, 3, 0, 1]
else
[0, 0, 3, 2, 1, 0, 0, 3, 2])
else
(if i.val < 3635 then
[0, 0, 3, 2, 1, 0, 0, 3, 3]
else
[0, 0, 3, 2, 1, 0, 3, 3, 0]))
else
(if i.val < 3638 then
(if i.val < 3637 then
[0, 0, 3, 2, 1, 0, 3, 3, 2]
else
[0, 0, 3, 2, 1, 1, 0, 0, 3])
else
(if i.val < 3639 then
[0, 0, 3, 2, 1, 1, 0, 3, 3]
else
[0, 0, 3, 2, 2, 1, 0, 3, 0])))
else
(if i.val < 3644 then
(if i.val < 3642 then
(if i.val < 3641 then
[0, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 0, 3, 2, 2, 1, 0, 3, 3])
else
(if i.val < 3643 then
[0, 0, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 3646 then
(if i.val < 3645 then
[0, 0, 3, 2, 2, 3, 0, 0, 3]
else
[0, 0, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 3647 then
[0, 0, 3, 3, 0, 0, 1, 2, 1]
else
[0, 0, 3, 3, 0, 0, 1, 2, 3]))))))
else
(if i.val < 3680 then
(if i.val < 3664 then
(if i.val < 3656 then
(if i.val < 3652 then
(if i.val < 3650 then
(if i.val < 3649 then
[0, 0, 3, 3, 0, 0, 2, 1, 1]
else
[0, 0, 3, 3, 0, 1, 1, 0, 3])
else
(if i.val < 3651 then
[0, 0, 3, 3, 0, 1, 1, 2, 2]
else
[0, 0, 3, 3, 0, 1, 2, 1, 1]))
else
(if i.val < 3654 then
(if i.val < 3653 then
[0, 0, 3, 3, 0, 1, 2, 2, 1]
else
[0, 0, 3, 3, 0, 1, 2, 2, 3])
else
(if i.val < 3655 then
[0, 0, 3, 3, 0, 1, 2, 3, 0]
else
[0, 0, 3, 3, 0, 2, 1, 0, 3])))
else
(if i.val < 3660 then
(if i.val < 3658 then
(if i.val < 3657 then
[0, 0, 3, 3, 0, 2, 1, 1, 3]
else
[0, 0, 3, 3, 0, 2, 1, 3, 2])
else
(if i.val < 3659 then
[0, 0, 3, 3, 0, 2, 2, 3, 3]
else
[0, 0, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 3662 then
(if i.val < 3661 then
[0, 0, 3, 3, 2, 1, 0, 3, 2]
else
[0, 0, 3, 3, 2, 1, 0, 3, 3])
else
(if i.val < 3663 then
[0, 0, 3, 3, 2, 1, 1, 0, 3]
else
[0, 0, 3, 3, 2, 1, 1, 2, 3]))))
else
(if i.val < 3672 then
(if i.val < 3668 then
(if i.val < 3666 then
(if i.val < 3665 then
[0, 1, 0, 0, 1, 2, 1, 0, 3]
else
[0, 1, 0, 0, 1, 2, 1, 1, 3])
else
(if i.val < 3667 then
[0, 1, 0, 0, 1, 2, 1, 3, 0]
else
[0, 1, 0, 0, 1, 2, 1, 3, 3]))
else
(if i.val < 3670 then
(if i.val < 3669 then
[0, 1, 0, 0, 1, 2, 2, 1, 3]
else
[0, 1, 0, 0, 1, 2, 2, 3, 0])
else
(if i.val < 3671 then
[0, 1, 0, 0, 1, 2, 2, 3, 2]
else
[0, 1, 0, 0, 1, 2, 2, 3, 3])))
else
(if i.val < 3676 then
(if i.val < 3674 then
(if i.val < 3673 then
[0, 1, 0, 0, 1, 2, 3, 0, 0]
else
[0, 1, 0, 0, 1, 2, 3, 0, 1])
else
(if i.val < 3675 then
[0, 1, 0, 0, 1, 2, 3, 2, 1]
else
[0, 1, 0, 0, 1, 2, 3, 3, 0]))
else
(if i.val < 3678 then
(if i.val < 3677 then
[0, 1, 0, 0, 1, 2, 3, 3, 2]
else
[0, 1, 0, 0, 1, 3, 0, 0, 1])
else
(if i.val < 3679 then
[0, 1, 0, 0, 1, 3, 0, 0, 3]
else
[0, 1, 0, 0, 1, 3, 0, 1, 2])))))
else
(if i.val < 3696 then
(if i.val < 3688 then
(if i.val < 3684 then
(if i.val < 3682 then
(if i.val < 3681 then
[0, 1, 0, 0, 1, 3, 0, 2, 1]
else
[0, 1, 0, 0, 1, 3, 2, 1, 1])
else
(if i.val < 3683 then
[0, 1, 0, 0, 1, 3, 2, 2, 1]
else
[0, 1, 0, 0, 1, 3, 2, 2, 3]))
else
(if i.val < 3686 then
(if i.val < 3685 then
[0, 1, 0, 0, 1, 3, 3, 0, 1]
else
[0, 1, 0, 0, 1, 3, 3, 2, 1])
else
(if i.val < 3687 then
[0, 1, 0, 0, 1, 3, 3, 2, 2]
else
[0, 1, 0, 0, 2, 1, 0, 0, 3])))
else
(if i.val < 3692 then
(if i.val < 3690 then
(if i.val < 3689 then
[0, 1, 0, 0, 2, 1, 0, 3, 2]
else
[0, 1, 0, 0, 2, 1, 1, 2, 3])
else
(if i.val < 3691 then
[0, 1, 0, 0, 2, 1, 3, 0, 0]
else
[0, 1, 0, 0, 2, 1, 3, 0, 1]))
else
(if i.val < 3694 then
(if i.val < 3693 then
[0, 1, 0, 0, 2, 1, 3, 3, 2]
else
[0, 1, 0, 0, 2, 2, 1, 0, 3])
else
(if i.val < 3695 then
[0, 1, 0, 0, 2, 2, 1, 1, 3]
else
[0, 1, 0, 0, 2, 2, 1, 3, 2]))))
else
(if i.val < 3704 then
(if i.val < 3700 then
(if i.val < 3698 then
(if i.val < 3697 then
[0, 1, 0, 0, 2, 2, 1, 3, 3]
else
[0, 1, 0, 0, 2, 2, 3, 0, 0])
else
(if i.val < 3699 then
[0, 1, 0, 0, 2, 2, 3, 0, 1]
else
[0, 1, 0, 0, 2, 2, 3, 2, 2]))
else
(if i.val < 3702 then
(if i.val < 3701 then
[0, 1, 0, 0, 2, 2, 3, 3, 2]
else
[0, 1, 0, 0, 2, 3, 0, 0, 1])
else
(if i.val < 3703 then
[0, 1, 0, 0, 2, 3, 0, 0, 3]
else
[0, 1, 0, 0, 2, 3, 0, 2, 1])))
else
(if i.val < 3708 then
(if i.val < 3706 then
(if i.val < 3705 then
[0, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 1, 0, 0, 2, 3, 0, 2, 3])
else
(if i.val < 3707 then
[0, 1, 0, 0, 2, 3, 2, 1, 1]
else
[0, 1, 0, 0, 2, 3, 3, 0, 0]))
else
(if i.val < 3710 then
(if i.val < 3709 then
[0, 1, 0, 0, 2, 3, 3, 0, 1]
else
[0, 1, 0, 0, 3, 0, 0, 1, 3])
else
(if i.val < 3711 then
[0, 1, 0, 0, 3, 0, 0, 2, 1]
else
[0, 1, 0, 0, 3, 0, 0, 2, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0029 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3776 then
(if i.val < 3744 then
(if i.val < 3728 then
(if i.val < 3720 then
(if i.val < 3716 then
(if i.val < 3714 then
(if i.val < 3713 then
[0, 1, 0, 0, 3, 0, 0, 2, 3]
else
[0, 1, 0, 0, 3, 0, 0, 3, 2])
else
(if i.val < 3715 then
[0, 1, 0, 0, 3, 0, 1, 2, 1]
else
[0, 1, 0, 0, 3, 0, 1, 2, 2]))
else
(if i.val < 3718 then
(if i.val < 3717 then
[0, 1, 0, 0, 3, 0, 2, 1, 1]
else
[0, 1, 0, 0, 3, 0, 2, 2, 1])
else
(if i.val < 3719 then
[0, 1, 0, 0, 3, 2, 1, 0, 3]
else
[0, 1, 0, 0, 3, 2, 2, 1, 1])))
else
(if i.val < 3724 then
(if i.val < 3722 then
(if i.val < 3721 then
[0, 1, 0, 0, 3, 2, 2, 1, 3]
else
[0, 1, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 3723 then
[0, 1, 0, 0, 3, 3, 0, 0, 1]
else
[0, 1, 0, 0, 3, 3, 0, 2, 1]))
else
(if i.val < 3726 then
(if i.val < 3725 then
[0, 1, 0, 0, 3, 3, 0, 2, 2]
else
[0, 1, 0, 0, 3, 3, 2, 1, 1])
else
(if i.val < 3727 then
[0, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 1, 0, 2, 1, 0, 0, 3, 3]))))
else
(if i.val < 3736 then
(if i.val < 3732 then
(if i.val < 3730 then
(if i.val < 3729 then
[0, 1, 0, 2, 1, 0, 3, 3, 2]
else
[0, 1, 0, 2, 1, 1, 0, 0, 3])
else
(if i.val < 3731 then
[0, 1, 0, 2, 1, 1, 0, 3, 0]
else
[0, 1, 0, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 3734 then
(if i.val < 3733 then
[0, 1, 0, 2, 1, 1, 0, 3, 3]
else
[0, 1, 0, 2, 1, 1, 2, 3, 2])
else
(if i.val < 3735 then
[0, 1, 0, 2, 1, 1, 3, 0, 0]
else
[0, 1, 0, 2, 1, 3, 0, 0, 3])))
else
(if i.val < 3740 then
(if i.val < 3738 then
(if i.val < 3737 then
[0, 1, 0, 2, 1, 3, 0, 1, 2]
else
[0, 1, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 3739 then
[0, 1, 0, 2, 1, 3, 3, 0, 0]
else
[0, 1, 0, 2, 1, 3, 3, 0, 1]))
else
(if i.val < 3742 then
(if i.val < 3741 then
[0, 1, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 0, 2, 2, 1, 0, 0, 3])
else
(if i.val < 3743 then
[0, 1, 0, 2, 2, 1, 0, 3, 0]
else
[0, 1, 0, 2, 2, 1, 0, 3, 2])))))
else
(if i.val < 3760 then
(if i.val < 3752 then
(if i.val < 3748 then
(if i.val < 3746 then
(if i.val < 3745 then
[0, 1, 0, 2, 2, 1, 0, 3, 3]
else
[0, 1, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 3747 then
[0, 1, 0, 2, 2, 1, 3, 0, 0]
else
[0, 1, 0, 2, 2, 1, 3, 0, 1]))
else
(if i.val < 3750 then
(if i.val < 3749 then
[0, 1, 0, 2, 2, 1, 3, 2, 1]
else
[0, 1, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 3751 then
[0, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 1, 0, 2, 2, 3, 0, 2, 1])))
else
(if i.val < 3756 then
(if i.val < 3754 then
(if i.val < 3753 then
[0, 1, 0, 2, 2, 3, 2, 2, 1]
else
[0, 1, 0, 2, 2, 3, 2, 2, 3])
else
(if i.val < 3755 then
[0, 1, 0, 2, 2, 3, 3, 0, 0]
else
[0, 1, 0, 2, 2, 3, 3, 2, 1]))
else
(if i.val < 3758 then
(if i.val < 3757 then
[0, 1, 0, 2, 2, 3, 3, 2, 2]
else
[0, 1, 0, 2, 3, 0, 0, 2, 1])
else
(if i.val < 3759 then
[0, 1, 0, 2, 3, 0, 0, 2, 3]
else
[0, 1, 0, 2, 3, 0, 0, 3, 2]))))
else
(if i.val < 3768 then
(if i.val < 3764 then
(if i.val < 3762 then
(if i.val < 3761 then
[0, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 1, 0, 2, 3, 0, 1, 2, 2])
else
(if i.val < 3763 then
[0, 1, 0, 2, 3, 0, 2, 1, 3]
else
[0, 1, 0, 2, 3, 2, 1, 0, 0]))
else
(if i.val < 3766 then
(if i.val < 3765 then
[0, 1, 0, 2, 3, 2, 1, 0, 3]
else
[0, 1, 0, 2, 3, 2, 2, 3, 0])
else
(if i.val < 3767 then
[0, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 1, 0, 2, 3, 3, 0, 2, 1])))
else
(if i.val < 3772 then
(if i.val < 3770 then
(if i.val < 3769 then
[0, 1, 0, 2, 3, 3, 0, 2, 2]
else
[0, 1, 0, 3, 0, 0, 1, 1, 3])
else
(if i.val < 3771 then
[0, 1, 0, 3, 0, 0, 1, 2, 1]
else
[0, 1, 0, 3, 0, 0, 1, 3, 2]))
else
(if i.val < 3774 then
(if i.val < 3773 then
[0, 1, 0, 3, 0, 0, 2, 1, 1]
else
[0, 1, 0, 3, 0, 0, 2, 2, 1])
else
(if i.val < 3775 then
[0, 1, 0, 3, 0, 0, 3, 2, 1]
else
[0, 1, 0, 3, 0, 0, 3, 2, 2]))))))
else
(if i.val < 3808 then
(if i.val < 3792 then
(if i.val < 3784 then
(if i.val < 3780 then
(if i.val < 3778 then
(if i.val < 3777 then
[0, 1, 0, 3, 0, 1, 1, 2, 1]
else
[0, 1, 0, 3, 0, 1, 1, 2, 2])
else
(if i.val < 3779 then
[0, 1, 0, 3, 0, 1, 2, 1, 1]
else
[0, 1, 0, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 3782 then
(if i.val < 3781 then
[0, 1, 0, 3, 0, 1, 2, 2, 3]
else
[0, 1, 0, 3, 0, 1, 2, 3, 0])
else
(if i.val < 3783 then
[0, 1, 0, 3, 0, 1, 2, 3, 3]
else
[0, 1, 0, 3, 0, 2, 1, 0, 3])))
else
(if i.val < 3788 then
(if i.val < 3786 then
(if i.val < 3785 then
[0, 1, 0, 3, 0, 2, 1, 1, 3]
else
[0, 1, 0, 3, 0, 2, 1, 3, 3])
else
(if i.val < 3787 then
[0, 1, 0, 3, 0, 2, 2, 1, 3]
else
[0, 1, 0, 3, 0, 2, 2, 3, 0]))
else
(if i.val < 3790 then
(if i.val < 3789 then
[0, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 1, 0, 3, 2, 1, 1, 0, 0])
else
(if i.val < 3791 then
[0, 1, 0, 3, 2, 2, 1, 0, 0]
else
[0, 1, 0, 3, 2, 2, 1, 0, 3]))))
else
(if i.val < 3800 then
(if i.val < 3796 then
(if i.val < 3794 then
(if i.val < 3793 then
[0, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 1, 0, 3, 2, 2, 1, 3, 2])
else
(if i.val < 3795 then
[0, 1, 0, 3, 2, 2, 3, 0, 0]
else
[0, 1, 0, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 3798 then
(if i.val < 3797 then
[0, 1, 0, 3, 3, 0, 0, 2, 3]
else
[0, 1, 0, 3, 3, 0, 1, 2, 1])
else
(if i.val < 3799 then
[0, 1, 0, 3, 3, 0, 1, 2, 3]
else
[0, 1, 0, 3, 3, 0, 2, 1, 3])))
else
(if i.val < 3804 then
(if i.val < 3802 then
(if i.val < 3801 then
[0, 1, 0, 3, 3, 0, 2, 2, 1]
else
[0, 1, 0, 3, 3, 0, 2, 2, 3])
else
(if i.val < 3803 then
[0, 1, 0, 3, 3, 0, 2, 3, 3]
else
[0, 1, 0, 3, 3, 2, 1, 0, 3]))
else
(if i.val < 3806 then
(if i.val < 3805 then
[0, 1, 1, 0, 0, 2, 1, 0, 3]
else
[0, 1, 1, 0, 0, 2, 1, 1, 3])
else
(if i.val < 3807 then
[0, 1, 1, 0, 0, 2, 1, 3, 0]
else
[0, 1, 1, 0, 0, 2, 1, 3, 3])))))
else
(if i.val < 3824 then
(if i.val < 3816 then
(if i.val < 3812 then
(if i.val < 3810 then
(if i.val < 3809 then
[0, 1, 1, 0, 0, 2, 2, 1, 3]
else
[0, 1, 1, 0, 0, 2, 2, 3, 0])
else
(if i.val < 3811 then
[0, 1, 1, 0, 0, 2, 2, 3, 2]
else
[0, 1, 1, 0, 0, 2, 2, 3, 3]))
else
(if i.val < 3814 then
(if i.val < 3813 then
[0, 1, 1, 0, 0, 2, 3, 0, 1]
else
[0, 1, 1, 0, 0, 2, 3, 2, 1])
else
(if i.val < 3815 then
[0, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 1, 1, 0, 0, 3, 0, 0, 3])))
else
(if i.val < 3820 then
(if i.val < 3818 then
(if i.val < 3817 then
[0, 1, 1, 0, 0, 3, 0, 1, 2]
else
[0, 1, 1, 0, 0, 3, 0, 2, 1])
else
(if i.val < 3819 then
[0, 1, 1, 0, 0, 3, 2, 1, 1]
else
[0, 1, 1, 0, 0, 3, 2, 2, 3]))
else
(if i.val < 3822 then
(if i.val < 3821 then
[0, 1, 1, 0, 0, 3, 3, 2, 2]
else
[0, 1, 1, 0, 2, 1, 0, 0, 3])
else
(if i.val < 3823 then
[0, 1, 1, 0, 2, 1, 0, 3, 0]
else
[0, 1, 1, 0, 2, 1, 0, 3, 2]))))
else
(if i.val < 3832 then
(if i.val < 3828 then
(if i.val < 3826 then
(if i.val < 3825 then
[0, 1, 1, 0, 2, 1, 0, 3, 3]
else
[0, 1, 1, 0, 2, 1, 1, 0, 0])
else
(if i.val < 3827 then
[0, 1, 1, 0, 2, 1, 1, 2, 3]
else
[0, 1, 1, 0, 2, 1, 3, 0, 1]))
else
(if i.val < 3830 then
(if i.val < 3829 then
[0, 1, 1, 0, 2, 1, 3, 3, 2]
else
[0, 1, 1, 0, 2, 2, 1, 0, 3])
else
(if i.val < 3831 then
[0, 1, 1, 0, 2, 2, 1, 1, 3]
else
[0, 1, 1, 0, 2, 2, 1, 3, 0])))
else
(if i.val < 3836 then
(if i.val < 3834 then
(if i.val < 3833 then
[0, 1, 1, 0, 2, 2, 1, 3, 2]
else
[0, 1, 1, 0, 2, 2, 1, 3, 3])
else
(if i.val < 3835 then
[0, 1, 1, 0, 2, 2, 3, 0, 0]
else
[0, 1, 1, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 3838 then
(if i.val < 3837 then
[0, 1, 1, 0, 2, 2, 3, 2, 1]
else
[0, 1, 1, 0, 2, 2, 3, 3, 2])
else
(if i.val < 3839 then
[0, 1, 1, 0, 2, 3, 0, 1, 2]
else
[0, 1, 1, 0, 2, 3, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0030 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3904 then
(if i.val < 3872 then
(if i.val < 3856 then
(if i.val < 3848 then
(if i.val < 3844 then
(if i.val < 3842 then
(if i.val < 3841 then
[0, 1, 1, 0, 2, 3, 0, 2, 2]
else
[0, 1, 1, 0, 2, 3, 2, 2, 3])
else
(if i.val < 3843 then
[0, 1, 1, 0, 2, 3, 3, 0, 1]
else
[0, 1, 1, 0, 3, 0, 0, 2, 2]))
else
(if i.val < 3846 then
(if i.val < 3845 then
[0, 1, 1, 0, 3, 0, 1, 2, 1]
else
[0, 1, 1, 0, 3, 0, 2, 1, 1])
else
(if i.val < 3847 then
[0, 1, 1, 0, 3, 0, 2, 1, 3]
else
[0, 1, 1, 0, 3, 0, 2, 2, 1])))
else
(if i.val < 3852 then
(if i.val < 3850 then
(if i.val < 3849 then
[0, 1, 1, 0, 3, 0, 2, 2, 3]
else
[0, 1, 1, 0, 3, 2, 1, 0, 3])
else
(if i.val < 3851 then
[0, 1, 1, 0, 3, 2, 2, 3, 0]
else
[0, 1, 1, 0, 3, 3, 0, 1, 2]))
else
(if i.val < 3854 then
(if i.val < 3853 then
[0, 1, 1, 0, 3, 3, 0, 2, 1]
else
[0, 1, 1, 0, 3, 3, 0, 2, 2])
else
(if i.val < 3855 then
[0, 1, 1, 0, 3, 3, 2, 1, 1]
else
[0, 1, 1, 0, 3, 3, 2, 2, 1]))))
else
(if i.val < 3864 then
(if i.val < 3860 then
(if i.val < 3858 then
(if i.val < 3857 then
[0, 1, 1, 2, 1, 0, 0, 1, 3]
else
[0, 1, 1, 2, 1, 0, 0, 3, 3])
else
(if i.val < 3859 then
[0, 1, 1, 2, 1, 0, 3, 0, 1]
else
[0, 1, 1, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 3862 then
(if i.val < 3861 then
[0, 1, 1, 2, 1, 0, 3, 3, 2]
else
[0, 1, 1, 2, 1, 1, 0, 3, 3])
else
(if i.val < 3863 then
[0, 1, 1, 2, 1, 1, 2, 3, 2]
else
[0, 1, 1, 2, 1, 1, 2, 3, 3])))
else
(if i.val < 3868 then
(if i.val < 3866 then
(if i.val < 3865 then
[0, 1, 1, 2, 1, 1, 3, 0, 0]
else
[0, 1, 1, 2, 1, 1, 3, 0, 1])
else
(if i.val < 3867 then
[0, 1, 1, 2, 1, 1, 3, 2, 2]
else
[0, 1, 1, 2, 1, 1, 3, 3, 2]))
else
(if i.val < 3870 then
(if i.val < 3869 then
[0, 1, 1, 2, 1, 3, 0, 0, 3]
else
[0, 1, 1, 2, 1, 3, 0, 1, 2])
else
(if i.val < 3871 then
[0, 1, 1, 2, 1, 3, 0, 2, 2]
else
[0, 1, 1, 2, 1, 3, 2, 1, 1])))))
else
(if i.val < 3888 then
(if i.val < 3880 then
(if i.val < 3876 then
(if i.val < 3874 then
(if i.val < 3873 then
[0, 1, 1, 2, 1, 3, 2, 2, 1]
else
[0, 1, 1, 2, 1, 3, 2, 2, 3])
else
(if i.val < 3875 then
[0, 1, 1, 2, 1, 3, 3, 0, 0]
else
[0, 1, 1, 2, 1, 3, 3, 2, 1]))
else
(if i.val < 3878 then
(if i.val < 3877 then
[0, 1, 1, 2, 1, 3, 3, 2, 2]
else
[0, 1, 1, 2, 2, 1, 0, 3, 0])
else
(if i.val < 3879 then
[0, 1, 1, 2, 2, 1, 0, 3, 2]
else
[0, 1, 1, 2, 2, 1, 0, 3, 3])))
else
(if i.val < 3884 then
(if i.val < 3882 then
(if i.val < 3881 then
[0, 1, 1, 2, 2, 1, 1, 3, 2]
else
[0, 1, 1, 2, 2, 1, 1, 3, 3])
else
(if i.val < 3883 then
[0, 1, 1, 2, 2, 1, 3, 0, 0]
else
[0, 1, 1, 2, 2, 1, 3, 0, 1]))
else
(if i.val < 3886 then
(if i.val < 3885 then
[0, 1, 1, 2, 2, 1, 3, 3, 2]
else
[0, 1, 1, 2, 2, 3, 0, 0, 3])
else
(if i.val < 3887 then
[0, 1, 1, 2, 2, 3, 0, 1, 2]
else
[0, 1, 1, 2, 2, 3, 2, 1, 1]))))
else
(if i.val < 3896 then
(if i.val < 3892 then
(if i.val < 3890 then
(if i.val < 3889 then
[0, 1, 1, 2, 2, 3, 2, 2, 1]
else
[0, 1, 1, 2, 2, 3, 2, 2, 3])
else
(if i.val < 3891 then
[0, 1, 1, 2, 2, 3, 3, 2, 2]
else
[0, 1, 1, 2, 3, 0, 0, 1, 1]))
else
(if i.val < 3894 then
(if i.val < 3893 then
[0, 1, 1, 2, 3, 0, 0, 2, 1]
else
[0, 1, 1, 2, 3, 0, 0, 2, 2])
else
(if i.val < 3895 then
[0, 1, 1, 2, 3, 0, 0, 2, 3]
else
[0, 1, 1, 2, 3, 0, 0, 3, 2])))
else
(if i.val < 3900 then
(if i.val < 3898 then
(if i.val < 3897 then
[0, 1, 1, 2, 3, 0, 1, 2, 1]
else
[0, 1, 1, 2, 3, 0, 1, 2, 2])
else
(if i.val < 3899 then
[0, 1, 1, 2, 3, 0, 2, 1, 1]
else
[0, 1, 1, 2, 3, 0, 2, 1, 3]))
else
(if i.val < 3902 then
(if i.val < 3901 then
[0, 1, 1, 2, 3, 0, 2, 2, 1]
else
[0, 1, 1, 2, 3, 2, 1, 0, 0])
else
(if i.val < 3903 then
[0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 1, 1, 2, 3, 3, 0, 0, 1]))))))
else
(if i.val < 3936 then
(if i.val < 3920 then
(if i.val < 3912 then
(if i.val < 3908 then
(if i.val < 3906 then
(if i.val < 3905 then
[0, 1, 1, 2, 3, 3, 0, 1, 2]
else
[0, 1, 1, 2, 3, 3, 0, 2, 2])
else
(if i.val < 3907 then
[0, 1, 1, 2, 3, 3, 0, 2, 3]
else
[0, 1, 1, 3, 0, 0, 1, 1, 3]))
else
(if i.val < 3910 then
(if i.val < 3909 then
[0, 1, 1, 3, 0, 0, 1, 2, 1]
else
[0, 1, 1, 3, 0, 0, 2, 1, 1])
else
(if i.val < 3911 then
[0, 1, 1, 3, 0, 0, 2, 2, 1]
else
[0, 1, 1, 3, 0, 0, 3, 2, 1])))
else
(if i.val < 3916 then
(if i.val < 3914 then
(if i.val < 3913 then
[0, 1, 1, 3, 0, 0, 3, 2, 2]
else
[0, 1, 1, 3, 0, 1, 1, 2, 1])
else
(if i.val < 3915 then
[0, 1, 1, 3, 0, 1, 2, 2, 3]
else
[0, 1, 1, 3, 0, 1, 2, 3, 0]))
else
(if i.val < 3918 then
(if i.val < 3917 then
[0, 1, 1, 3, 0, 1, 2, 3, 3]
else
[0, 1, 1, 3, 0, 2, 1, 0, 3])
else
(if i.val < 3919 then
[0, 1, 1, 3, 0, 2, 1, 1, 3]
else
[0, 1, 1, 3, 0, 2, 1, 3, 2]))))
else
(if i.val < 3928 then
(if i.val < 3924 then
(if i.val < 3922 then
(if i.val < 3921 then
[0, 1, 1, 3, 0, 2, 2, 3, 0]
else
[0, 1, 1, 3, 0, 2, 2, 3, 3])
else
(if i.val < 3923 then
[0, 1, 1, 3, 2, 1, 0, 0, 3]
else
[0, 1, 1, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 3926 then
(if i.val < 3925 then
[0, 1, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 1, 3, 3, 0, 0, 2, 1])
else
(if i.val < 3927 then
[0, 1, 1, 3, 3, 0, 1, 2, 1]
else
[0, 1, 1, 3, 3, 0, 1, 2, 2])))
else
(if i.val < 3932 then
(if i.val < 3930 then
(if i.val < 3929 then
[0, 1, 1, 3, 3, 0, 1, 2, 3]
else
[0, 1, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 3931 then
[0, 1, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 2, 1, 0, 0, 1, 2, 3]))
else
(if i.val < 3934 then
(if i.val < 3933 then
[0, 1, 2, 1, 0, 0, 1, 3, 3]
else
[0, 1, 2, 1, 0, 0, 3, 0, 0])
else
(if i.val < 3935 then
[0, 1, 2, 1, 0, 0, 3, 0, 1]
else
[0, 1, 2, 1, 0, 0, 3, 3, 2])))))
else
(if i.val < 3952 then
(if i.val < 3944 then
(if i.val < 3940 then
(if i.val < 3938 then
(if i.val < 3937 then
[0, 1, 2, 1, 0, 3, 0, 0, 3]
else
[0, 1, 2, 1, 0, 3, 0, 1, 2])
else
(if i.val < 3939 then
[0, 1, 2, 1, 0, 3, 0, 2, 1]
else
[0, 1, 2, 1, 0, 3, 0, 2, 2]))
else
(if i.val < 3942 then
(if i.val < 3941 then
[0, 1, 2, 1, 0, 3, 2, 1, 1]
else
[0, 1, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 3943 then
[0, 1, 2, 1, 1, 0, 0, 3, 0]
else
[0, 1, 2, 1, 1, 0, 0, 3, 2])))
else
(if i.val < 3948 then
(if i.val < 3946 then
(if i.val < 3945 then
[0, 1, 2, 1, 1, 0, 0, 3, 3]
else
[0, 1, 2, 1, 1, 0, 2, 1, 3])
else
(if i.val < 3947 then
[0, 1, 2, 1, 1, 0, 2, 3, 2]
else
[0, 1, 2, 1, 1, 0, 3, 0, 1]))
else
(if i.val < 3950 then
(if i.val < 3949 then
[0, 1, 2, 1, 1, 0, 3, 2, 1]
else
[0, 1, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 3951 then
[0, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 1, 2, 1, 1, 2, 3, 2, 1]))))
else
(if i.val < 3960 then
(if i.val < 3956 then
(if i.val < 3954 then
(if i.val < 3953 then
[0, 1, 2, 1, 1, 3, 0, 1, 2]
else
[0, 1, 2, 1, 1, 3, 0, 2, 2])
else
(if i.val < 3955 then
[0, 1, 2, 1, 1, 3, 2, 1, 1]
else
[0, 1, 2, 1, 1, 3, 2, 2, 1]))
else
(if i.val < 3958 then
(if i.val < 3957 then
[0, 1, 2, 1, 1, 3, 2, 2, 3]
else
[0, 1, 2, 1, 1, 3, 3, 2, 2])
else
(if i.val < 3959 then
[0, 1, 2, 1, 3, 0, 0, 2, 2]
else
[0, 1, 2, 1, 3, 0, 0, 2, 3])))
else
(if i.val < 3964 then
(if i.val < 3962 then
(if i.val < 3961 then
[0, 1, 2, 1, 3, 0, 0, 3, 2]
else
[0, 1, 2, 1, 3, 0, 1, 2, 1])
else
(if i.val < 3963 then
[0, 1, 2, 1, 3, 0, 1, 2, 2]
else
[0, 1, 2, 1, 3, 0, 1, 2, 3]))
else
(if i.val < 3966 then
(if i.val < 3965 then
[0, 1, 2, 1, 3, 0, 2, 2, 3]
else
[0, 1, 2, 1, 3, 2, 1, 0, 0])
else
(if i.val < 3967 then
[0, 1, 2, 1, 3, 2, 1, 0, 3]
else
[0, 1, 2, 1, 3, 2, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0031 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4032 then
(if i.val < 4000 then
(if i.val < 3984 then
(if i.val < 3976 then
(if i.val < 3972 then
(if i.val < 3970 then
(if i.val < 3969 then
[0, 1, 2, 1, 3, 3, 0, 0, 1]
else
[0, 1, 2, 1, 3, 3, 0, 1, 2])
else
(if i.val < 3971 then
[0, 1, 2, 1, 3, 3, 0, 2, 3]
else
[0, 1, 2, 2, 1, 0, 0, 3, 0]))
else
(if i.val < 3974 then
(if i.val < 3973 then
[0, 1, 2, 2, 1, 0, 0, 3, 3]
else
[0, 1, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 3975 then
[0, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 1, 2, 2, 1, 1, 3, 0, 1])))
else
(if i.val < 3980 then
(if i.val < 3978 then
(if i.val < 3977 then
[0, 1, 2, 2, 1, 3, 0, 0, 1]
else
[0, 1, 2, 2, 1, 3, 0, 2, 3])
else
(if i.val < 3979 then
[0, 1, 2, 2, 1, 3, 2, 1, 1]
else
[0, 1, 2, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 3982 then
(if i.val < 3981 then
[0, 1, 2, 2, 1, 3, 3, 0, 0]
else
[0, 1, 2, 2, 3, 0, 0, 2, 3])
else
(if i.val < 3983 then
[0, 1, 2, 2, 3, 0, 1, 2, 2]
else
[0, 1, 2, 2, 3, 0, 1, 2, 3]))))
else
(if i.val < 3992 then
(if i.val < 3988 then
(if i.val < 3986 then
(if i.val < 3985 then
[0, 1, 2, 2, 3, 0, 2, 2, 3]
else
[0, 1, 2, 2, 3, 2, 1, 0, 0])
else
(if i.val < 3987 then
[0, 1, 2, 2, 3, 2, 1, 0, 3]
else
[0, 1, 2, 2, 3, 2, 2, 1, 1]))
else
(if i.val < 3990 then
(if i.val < 3989 then
[0, 1, 2, 2, 3, 2, 2, 1, 3]
else
[0, 1, 2, 2, 3, 3, 0, 2, 3])
else
(if i.val < 3991 then
[0, 1, 2, 3, 0, 0, 1, 1, 3]
else
[0, 1, 2, 3, 0, 0, 1, 2, 1])))
else
(if i.val < 3996 then
(if i.val < 3994 then
(if i.val < 3993 then
[0, 1, 2, 3, 0, 0, 1, 2, 3]
else
[0, 1, 2, 3, 0, 0, 1, 3, 2])
else
(if i.val < 3995 then
[0, 1, 2, 3, 0, 0, 2, 2, 1]
else
[0, 1, 2, 3, 0, 0, 2, 2, 3]))
else
(if i.val < 3998 then
(if i.val < 3997 then
[0, 1, 2, 3, 0, 0, 2, 3, 3]
else
[0, 1, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 3999 then
[0, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 1, 2, 3, 0, 1, 1, 2, 2])))))
else
(if i.val < 4016 then
(if i.val < 4008 then
(if i.val < 4004 then
(if i.val < 4002 then
(if i.val < 4001 then
[0, 1, 2, 3, 0, 1, 2, 1, 1]
else
[0, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 4003 then
[0, 1, 2, 3, 0, 1, 2, 3, 3]
else
[0, 1, 2, 3, 0, 2, 1, 1, 3]))
else
(if i.val < 4006 then
(if i.val < 4005 then
[0, 1, 2, 3, 0, 2, 2, 1, 3]
else
[0, 1, 2, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4007 then
[0, 1, 2, 3, 0, 2, 2, 3, 3]
else
[0, 1, 2, 3, 0, 2, 3, 3, 0])))
else
(if i.val < 4012 then
(if i.val < 4010 then
(if i.val < 4009 then
[0, 1, 2, 3, 2, 1, 0, 0, 3]
else
[0, 1, 2, 3, 2, 1, 0, 3, 3])
else
(if i.val < 4011 then
[0, 1, 2, 3, 2, 1, 1, 2, 3]
else
[0, 1, 2, 3, 2, 2, 1, 1, 3]))
else
(if i.val < 4014 then
(if i.val < 4013 then
[0, 1, 2, 3, 2, 2, 3, 0, 0]
else
[0, 1, 2, 3, 3, 0, 0, 1, 1])
else
(if i.val < 4015 then
[0, 1, 2, 3, 3, 0, 0, 2, 1]
else
[0, 1, 2, 3, 3, 0, 0, 2, 3]))))
else
(if i.val < 4024 then
(if i.val < 4020 then
(if i.val < 4018 then
(if i.val < 4017 then
[0, 1, 2, 3, 3, 0, 1, 2, 1]
else
[0, 1, 2, 3, 3, 0, 1, 2, 2])
else
(if i.val < 4019 then
[0, 1, 2, 3, 3, 0, 2, 1, 3]
else
[0, 1, 2, 3, 3, 0, 2, 2, 1]))
else
(if i.val < 4022 then
(if i.val < 4021 then
[0, 1, 2, 3, 3, 0, 2, 2, 3]
else
[0, 1, 2, 3, 3, 0, 2, 3, 3])
else
(if i.val < 4023 then
[0, 1, 2, 3, 3, 2, 1, 0, 0]
else
[0, 1, 2, 3, 3, 2, 1, 0, 3])))
else
(if i.val < 4028 then
(if i.val < 4026 then
(if i.val < 4025 then
[0, 1, 3, 0, 0, 1, 1, 2, 1]
else
[0, 1, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 4027 then
[0, 1, 3, 0, 0, 1, 2, 3, 0]
else
[0, 1, 3, 0, 0, 1, 2, 3, 2]))
else
(if i.val < 4030 then
(if i.val < 4029 then
[0, 1, 3, 0, 0, 1, 2, 3, 3]
else
[0, 1, 3, 0, 0, 1, 3, 2, 1])
else
(if i.val < 4031 then
[0, 1, 3, 0, 0, 2, 2, 3, 2]
else
[0, 1, 3, 0, 0, 2, 3, 3, 2]))))))
else
(if i.val < 4064 then
(if i.val < 4048 then
(if i.val < 4040 then
(if i.val < 4036 then
(if i.val < 4034 then
(if i.val < 4033 then
[0, 1, 3, 0, 0, 3, 2, 1, 1]
else
[0, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 4035 then
[0, 1, 3, 0, 0, 3, 2, 2, 3]
else
[0, 1, 3, 0, 1, 1, 0, 2, 1]))
else
(if i.val < 4038 then
(if i.val < 4037 then
[0, 1, 3, 0, 1, 1, 0, 2, 2]
else
[0, 1, 3, 0, 1, 1, 0, 3, 2])
else
(if i.val < 4039 then
[0, 1, 3, 0, 1, 1, 0, 3, 3]
else
[0, 1, 3, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 4044 then
(if i.val < 4042 then
(if i.val < 4041 then
[0, 1, 3, 0, 1, 2, 2, 1, 3]
else
[0, 1, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 4043 then
[0, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 1, 3, 0, 1, 2, 3, 3, 0]))
else
(if i.val < 4046 then
(if i.val < 4045 then
[0, 1, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 4047 then
[0, 1, 3, 0, 2, 1, 1, 0, 0]
else
[0, 1, 3, 0, 2, 1, 1, 0, 3]))))
else
(if i.val < 4056 then
(if i.val < 4052 then
(if i.val < 4050 then
(if i.val < 4049 then
[0, 1, 3, 0, 2, 1, 3, 3, 2]
else
[0, 1, 3, 0, 2, 2, 1, 0, 3])
else
(if i.val < 4051 then
[0, 1, 3, 0, 2, 2, 1, 1, 3]
else
[0, 1, 3, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 4054 then
(if i.val < 4053 then
[0, 1, 3, 0, 2, 3, 3, 0, 1]
else
[0, 1, 3, 2, 1, 0, 0, 3, 2])
else
(if i.val < 4055 then
[0, 1, 3, 2, 1, 0, 3, 3, 0]
else
[0, 1, 3, 2, 1, 1, 0, 0, 3])))
else
(if i.val < 4060 then
(if i.val < 4058 then
(if i.val < 4057 then
[0, 1, 3, 2, 2, 1, 0, 3, 0]
else
[0, 1, 3, 2, 2, 1, 0, 3, 3])
else
(if i.val < 4059 then
[0, 1, 3, 2, 2, 1, 1, 3, 2]
else
[0, 1, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 4062 then
(if i.val < 4061 then
[0, 1, 3, 3, 0, 0, 1, 2, 1]
else
[0, 1, 3, 3, 0, 0, 1, 2, 3])
else
(if i.val < 4063 then
[0, 1, 3, 3, 0, 1, 1, 2, 2]
else
[0, 1, 3, 3, 0, 1, 2, 2, 3])))))
else
(if i.val < 4080 then
(if i.val < 4072 then
(if i.val < 4068 then
(if i.val < 4066 then
(if i.val < 4065 then
[0, 1, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 3, 3, 0, 2, 1, 0, 3])
else
(if i.val < 4067 then
[0, 1, 3, 3, 0, 2, 1, 1, 3]
else
[0, 1, 3, 3, 0, 2, 1, 3, 2]))
else
(if i.val < 4070 then
(if i.val < 4069 then
[0, 1, 3, 3, 0, 2, 2, 3, 3]
else
[0, 1, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4071 then
[0, 1, 3, 3, 2, 1, 0, 3, 3]
else
[0, 1, 3, 3, 2, 1, 1, 2, 3])))
else
(if i.val < 4076 then
(if i.val < 4074 then
(if i.val < 4073 then
[0, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 2, 1, 0, 0, 1, 2, 3, 0])
else
(if i.val < 4075 then
[0, 2, 1, 0, 0, 1, 2, 3, 2]
else
[0, 2, 1, 0, 0, 1, 3, 0, 0]))
else
(if i.val < 4078 then
(if i.val < 4077 then
[0, 2, 1, 0, 0, 1, 3, 2, 1]
else
[0, 2, 1, 0, 0, 1, 3, 3, 2])
else
(if i.val < 4079 then
[0, 2, 1, 0, 0, 3, 0, 0, 3]
else
[0, 2, 1, 0, 0, 3, 2, 2, 1]))))
else
(if i.val < 4088 then
(if i.val < 4084 then
(if i.val < 4082 then
(if i.val < 4081 then
[0, 2, 1, 0, 0, 3, 2, 2, 3]
else
[0, 2, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 4083 then
[0, 2, 1, 0, 3, 0, 0, 1, 1]
else
[0, 2, 1, 0, 3, 0, 0, 2, 1]))
else
(if i.val < 4086 then
(if i.val < 4085 then
[0, 2, 1, 0, 3, 0, 1, 2, 1]
else
[0, 2, 1, 0, 3, 0, 1, 2, 2])
else
(if i.val < 4087 then
[0, 2, 1, 0, 3, 0, 1, 2, 3]
else
[0, 2, 1, 0, 3, 0, 2, 2, 1])))
else
(if i.val < 4092 then
(if i.val < 4090 then
(if i.val < 4089 then
[0, 2, 1, 0, 3, 2, 1, 0, 0]
else
[0, 2, 1, 0, 3, 2, 1, 0, 3])
else
(if i.val < 4091 then
[0, 2, 1, 0, 3, 2, 2, 1, 3]
else
[0, 2, 1, 0, 3, 2, 2, 3, 0]))
else
(if i.val < 4094 then
(if i.val < 4093 then
[0, 2, 1, 0, 3, 3, 0, 2, 2]
else
[0, 2, 1, 0, 3, 3, 0, 2, 3])
else
(if i.val < 4095 then
[0, 2, 1, 0, 3, 3, 2, 1, 1]
else
[0, 2, 1, 1, 0, 0, 2, 1, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0032 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4160 then
(if i.val < 4128 then
(if i.val < 4112 then
(if i.val < 4104 then
(if i.val < 4100 then
(if i.val < 4098 then
(if i.val < 4097 then
[0, 2, 1, 1, 0, 0, 3, 0, 0]
else
[0, 2, 1, 1, 0, 0, 3, 0, 1])
else
(if i.val < 4099 then
[0, 2, 1, 1, 0, 0, 3, 2, 1]
else
[0, 2, 1, 1, 0, 0, 3, 2, 2]))
else
(if i.val < 4102 then
(if i.val < 4101 then
[0, 2, 1, 1, 0, 0, 3, 3, 2]
else
[0, 2, 1, 1, 0, 2, 1, 1, 3])
else
(if i.val < 4103 then
[0, 2, 1, 1, 0, 2, 1, 3, 2]
else
[0, 2, 1, 1, 0, 2, 1, 3, 3])))
else
(if i.val < 4108 then
(if i.val < 4106 then
(if i.val < 4105 then
[0, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 2, 1, 1, 0, 2, 3, 3, 2])
else
(if i.val < 4107 then
[0, 2, 1, 1, 0, 3, 0, 0, 3]
else
[0, 2, 1, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 4110 then
(if i.val < 4109 then
[0, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 2, 1, 1, 0, 3, 0, 2, 2])
else
(if i.val < 4111 then
[0, 2, 1, 1, 0, 3, 2, 1, 1]
else
[0, 2, 1, 1, 0, 3, 2, 2, 3]))))
else
(if i.val < 4120 then
(if i.val < 4116 then
(if i.val < 4114 then
(if i.val < 4113 then
[0, 2, 1, 1, 2, 3, 0, 1, 2]
else
[0, 2, 1, 1, 2, 3, 2, 1, 1])
else
(if i.val < 4115 then
[0, 2, 1, 1, 2, 3, 2, 2, 3]
else
[0, 2, 1, 1, 3, 0, 0, 1, 1]))
else
(if i.val < 4118 then
(if i.val < 4117 then
[0, 2, 1, 1, 3, 0, 1, 2, 1]
else
[0, 2, 1, 1, 3, 0, 1, 2, 2])
else
(if i.val < 4119 then
[0, 2, 1, 1, 3, 0, 1, 2, 3]
else
[0, 2, 1, 1, 3, 0, 2, 1, 1])))
else
(if i.val < 4124 then
(if i.val < 4122 then
(if i.val < 4121 then
[0, 2, 1, 1, 3, 3, 0, 1, 2]
else
[0, 2, 1, 3, 0, 0, 1, 1, 3])
else
(if i.val < 4123 then
[0, 2, 1, 3, 0, 0, 1, 2, 1]
else
[0, 2, 1, 3, 0, 0, 1, 2, 3]))
else
(if i.val < 4126 then
(if i.val < 4125 then
[0, 2, 1, 3, 0, 0, 2, 2, 1]
else
[0, 2, 1, 3, 0, 0, 2, 2, 3])
else
(if i.val < 4127 then
[0, 2, 1, 3, 0, 0, 3, 2, 1]
else
[0, 2, 1, 3, 0, 0, 3, 2, 2])))))
else
(if i.val < 4144 then
(if i.val < 4136 then
(if i.val < 4132 then
(if i.val < 4130 then
(if i.val < 4129 then
[0, 2, 1, 3, 0, 2, 2, 3, 3]
else
[0, 2, 1, 3, 2, 1, 1, 0, 0])
else
(if i.val < 4131 then
[0, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 2, 1, 3, 2, 2, 1, 3, 2]))
else
(if i.val < 4134 then
(if i.val < 4133 then
[0, 2, 1, 3, 2, 2, 3, 0, 0]
else
[0, 2, 1, 3, 2, 2, 3, 0, 1])
else
(if i.val < 4135 then
[0, 2, 1, 3, 3, 0, 0, 2, 1]
else
[0, 2, 1, 3, 3, 0, 1, 2, 3])))
else
(if i.val < 4140 then
(if i.val < 4138 then
(if i.val < 4137 then
[0, 2, 1, 3, 3, 0, 2, 1, 3]
else
[0, 2, 1, 3, 3, 0, 2, 2, 3])
else
(if i.val < 4139 then
[0, 2, 1, 3, 3, 0, 2, 3, 3]
else
[0, 2, 1, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 4142 then
(if i.val < 4141 then
[0, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 2, 1, 3, 3, 2, 2, 1, 1])
else
(if i.val < 4143 then
[0, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 2, 2, 1, 0, 0, 3, 3, 2]))))
else
(if i.val < 4152 then
(if i.val < 4148 then
(if i.val < 4146 then
(if i.val < 4145 then
[0, 2, 2, 1, 0, 3, 0, 0, 1]
else
[0, 2, 2, 1, 0, 3, 0, 1, 2])
else
(if i.val < 4147 then
[0, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 2, 2, 1, 0, 3, 0, 2, 2]))
else
(if i.val < 4150 then
(if i.val < 4149 then
[0, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 2, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 4151 then
[0, 2, 2, 1, 1, 0, 0, 3, 0]
else
[0, 2, 2, 1, 1, 0, 3, 0, 1])))
else
(if i.val < 4156 then
(if i.val < 4154 then
(if i.val < 4153 then
[0, 2, 2, 1, 1, 0, 3, 2, 1]
else
[0, 2, 2, 1, 1, 0, 3, 3, 2])
else
(if i.val < 4155 then
[0, 2, 2, 1, 1, 3, 0, 1, 2]
else
[0, 2, 2, 1, 1, 3, 2, 1, 1]))
else
(if i.val < 4158 then
(if i.val < 4157 then
[0, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 2, 2, 1, 3, 0, 0, 2, 3])
else
(if i.val < 4159 then
[0, 2, 2, 1, 3, 0, 1, 2, 1]
else
[0, 2, 2, 1, 3, 0, 1, 2, 2]))))))
else
(if i.val < 4192 then
(if i.val < 4176 then
(if i.val < 4168 then
(if i.val < 4164 then
(if i.val < 4162 then
(if i.val < 4161 then
[0, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 2, 2, 1, 3, 2, 1, 0, 3])
else
(if i.val < 4163 then
[0, 2, 2, 1, 3, 2, 2, 1, 1]
else
[0, 2, 2, 1, 3, 2, 2, 1, 3]))
else
(if i.val < 4166 then
(if i.val < 4165 then
[0, 2, 2, 1, 3, 3, 0, 1, 2]
else
[0, 2, 2, 1, 3, 3, 0, 2, 3])
else
(if i.val < 4167 then
[0, 2, 2, 1, 3, 3, 2, 2, 1]
else
[0, 2, 2, 3, 0, 0, 1, 1, 3])))
else
(if i.val < 4172 then
(if i.val < 4170 then
(if i.val < 4169 then
[0, 2, 2, 3, 0, 0, 1, 2, 1]
else
[0, 2, 2, 3, 0, 0, 2, 1, 1])
else
(if i.val < 4171 then
[0, 2, 2, 3, 0, 0, 2, 2, 1]
else
[0, 2, 2, 3, 0, 0, 2, 2, 3]))
else
(if i.val < 4174 then
(if i.val < 4173 then
[0, 2, 2, 3, 0, 0, 3, 2, 2]
else
[0, 2, 2, 3, 0, 1, 1, 2, 2])
else
(if i.val < 4175 then
[0, 2, 2, 3, 0, 1, 2, 2, 1]
else
[0, 2, 2, 3, 0, 2, 1, 0, 3]))))
else
(if i.val < 4184 then
(if i.val < 4180 then
(if i.val < 4178 then
(if i.val < 4177 then
[0, 2, 2, 3, 0, 2, 1, 1, 3]
else
[0, 2, 2, 3, 0, 2, 3, 3, 2])
else
(if i.val < 4179 then
[0, 2, 2, 3, 2, 1, 0, 0, 3]
else
[0, 2, 2, 3, 2, 1, 0, 3, 3]))
else
(if i.val < 4182 then
(if i.val < 4181 then
[0, 2, 2, 3, 2, 1, 1, 2, 3]
else
[0, 2, 2, 3, 2, 2, 1, 0, 3])
else
(if i.val < 4183 then
[0, 2, 2, 3, 2, 2, 1, 1, 3]
else
[0, 2, 2, 3, 2, 2, 1, 3, 2])))
else
(if i.val < 4188 then
(if i.val < 4186 then
(if i.val < 4185 then
[0, 2, 2, 3, 3, 0, 0, 2, 3]
else
[0, 2, 2, 3, 3, 0, 2, 1, 3])
else
(if i.val < 4187 then
[0, 2, 2, 3, 3, 0, 2, 2, 3]
else
[0, 2, 2, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 4190 then
(if i.val < 4189 then
[0, 2, 3, 0, 0, 1, 1, 2, 2]
else
[0, 2, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 4191 then
[0, 2, 3, 0, 0, 1, 2, 3, 0]
else
[0, 2, 3, 0, 0, 1, 2, 3, 2])))))
else
(if i.val < 4208 then
(if i.val < 4200 then
(if i.val < 4196 then
(if i.val < 4194 then
(if i.val < 4193 then
[0, 2, 3, 0, 0, 1, 3, 0, 0]
else
[0, 2, 3, 0, 0, 1, 3, 2, 1])
else
(if i.val < 4195 then
[0, 2, 3, 0, 0, 2, 1, 0, 0]
else
[0, 2, 3, 0, 0, 2, 1, 1, 3]))
else
(if i.val < 4198 then
(if i.val < 4197 then
[0, 2, 3, 0, 0, 2, 2, 1, 1]
else
[0, 2, 3, 0, 0, 2, 2, 3, 2])
else
(if i.val < 4199 then
[0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 2, 3, 0, 1, 1, 0, 2, 1])))
else
(if i.val < 4204 then
(if i.val < 4202 then
(if i.val < 4201 then
[0, 2, 3, 0, 1, 1, 0, 2, 2]
else
[0, 2, 3, 0, 1, 1, 0, 3, 3])
else
(if i.val < 4203 then
[0, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 2, 3, 0, 1, 1, 2, 2, 1]))
else
(if i.val < 4206 then
(if i.val < 4205 then
[0, 2, 3, 0, 1, 1, 2, 3, 3]
else
[0, 2, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 4207 then
[0, 2, 3, 0, 1, 2, 2, 1, 3]
else
[0, 2, 3, 0, 1, 2, 2, 3, 0]))))
else
(if i.val < 4216 then
(if i.val < 4212 then
(if i.val < 4210 then
(if i.val < 4209 then
[0, 2, 3, 0, 1, 2, 3, 0, 0]
else
[0, 2, 3, 0, 1, 2, 3, 3, 2])
else
(if i.val < 4211 then
[0, 2, 3, 0, 2, 1, 0, 3, 2]
else
[0, 2, 3, 0, 2, 1, 1, 0, 3]))
else
(if i.val < 4214 then
(if i.val < 4213 then
[0, 2, 3, 0, 2, 1, 1, 2, 3]
else
[0, 2, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 4215 then
[0, 2, 3, 0, 2, 2, 3, 0, 1]
else
[0, 2, 3, 2, 1, 0, 3, 3, 0])))
else
(if i.val < 4220 then
(if i.val < 4218 then
(if i.val < 4217 then
[0, 2, 3, 2, 1, 1, 0, 3, 3]
else
[0, 2, 3, 2, 2, 1, 0, 3, 2])
else
(if i.val < 4219 then
[0, 2, 3, 2, 2, 1, 1, 3, 2]
else
[0, 2, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 4222 then
(if i.val < 4221 then
[0, 2, 3, 2, 2, 3, 0, 0, 3]
else
[0, 2, 3, 2, 2, 3, 0, 1, 2])
else
(if i.val < 4223 then
[0, 2, 3, 3, 0, 0, 1, 2, 1]
else
[0, 2, 3, 3, 0, 0, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0033 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4288 then
(if i.val < 4256 then
(if i.val < 4240 then
(if i.val < 4232 then
(if i.val < 4228 then
(if i.val < 4226 then
(if i.val < 4225 then
[0, 2, 3, 3, 0, 1, 1, 0, 3]
else
[0, 2, 3, 3, 0, 1, 1, 2, 2])
else
(if i.val < 4227 then
[0, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 2, 3, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 4230 then
(if i.val < 4229 then
[0, 2, 3, 3, 0, 2, 1, 1, 3]
else
[0, 2, 3, 3, 0, 2, 1, 3, 2])
else
(if i.val < 4231 then
[0, 2, 3, 3, 0, 2, 2, 3, 3]
else
[0, 2, 3, 3, 2, 1, 0, 3, 3])))
else
(if i.val < 4236 then
(if i.val < 4234 then
(if i.val < 4233 then
[0, 2, 3, 3, 2, 1, 1, 0, 3]
else
[0, 2, 3, 3, 2, 1, 1, 2, 3])
else
(if i.val < 4235 then
[0, 3, 0, 0, 1, 1, 2, 1, 3]
else
[0, 3, 0, 0, 1, 1, 2, 2, 1]))
else
(if i.val < 4238 then
(if i.val < 4237 then
[0, 3, 0, 0, 1, 1, 3, 2, 2]
else
[0, 3, 0, 0, 1, 2, 1, 1, 3])
else
(if i.val < 4239 then
[0, 3, 0, 0, 1, 2, 1, 3, 0]
else
[0, 3, 0, 0, 1, 2, 2, 1, 3]))))
else
(if i.val < 4248 then
(if i.val < 4244 then
(if i.val < 4242 then
(if i.val < 4241 then
[0, 3, 0, 0, 1, 2, 3, 0, 1]
else
[0, 3, 0, 0, 1, 2, 3, 2, 1])
else
(if i.val < 4243 then
[0, 3, 0, 0, 1, 2, 3, 3, 2]
else
[0, 3, 0, 0, 1, 3, 2, 2, 1]))
else
(if i.val < 4246 then
(if i.val < 4245 then
[0, 3, 0, 0, 2, 1, 1, 0, 0]
else
[0, 3, 0, 0, 2, 1, 1, 0, 3])
else
(if i.val < 4247 then
[0, 3, 0, 0, 2, 1, 1, 3, 3]
else
[0, 3, 0, 0, 2, 1, 3, 0, 0])))
else
(if i.val < 4252 then
(if i.val < 4250 then
(if i.val < 4249 then
[0, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 3, 0, 0, 2, 2, 1, 0, 3])
else
(if i.val < 4251 then
[0, 3, 0, 0, 2, 2, 1, 3, 3]
else
[0, 3, 0, 0, 2, 2, 3, 3, 2]))
else
(if i.val < 4254 then
(if i.val < 4253 then
[0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 3, 0, 0, 3, 2, 1, 0, 3])
else
(if i.val < 4255 then
[0, 3, 0, 0, 3, 2, 2, 1, 1]
else
[0, 3, 0, 0, 3, 2, 2, 3, 0])))))
else
(if i.val < 4272 then
(if i.val < 4264 then
(if i.val < 4260 then
(if i.val < 4258 then
(if i.val < 4257 then
[0, 3, 0, 1, 1, 0, 2, 2, 1]
else
[0, 3, 0, 1, 1, 0, 2, 2, 3])
else
(if i.val < 4259 then
[0, 3, 0, 1, 1, 0, 3, 2, 1]
else
[0, 3, 0, 1, 1, 0, 3, 3, 0]))
else
(if i.val < 4262 then
(if i.val < 4261 then
[0, 3, 0, 1, 1, 0, 3, 3, 2]
else
[0, 3, 0, 1, 1, 2, 2, 3, 0])
else
(if i.val < 4263 then
[0, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 3, 0, 1, 1, 2, 3, 3, 2])))
else
(if i.val < 4268 then
(if i.val < 4266 then
(if i.val < 4265 then
[0, 3, 0, 1, 2, 1, 1, 0, 3]
else
[0, 3, 0, 1, 2, 1, 1, 3, 0])
else
(if i.val < 4267 then
[0, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 3, 0, 1, 2, 2, 3, 0, 1]))
else
(if i.val < 4270 then
(if i.val < 4269 then
[0, 3, 0, 1, 2, 3, 3, 0, 0]
else
[0, 3, 0, 1, 2, 3, 3, 0, 1])
else
(if i.val < 4271 then
[0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[0, 3, 0, 2, 1, 0, 3, 3, 0]))))
else
(if i.val < 4280 then
(if i.val < 4276 then
(if i.val < 4274 then
(if i.val < 4273 then
[0, 3, 0, 2, 1, 1, 0, 3, 3]
else
[0, 3, 0, 2, 1, 1, 3, 2, 2])
else
(if i.val < 4275 then
[0, 3, 0, 2, 1, 3, 3, 0, 0]
else
[0, 3, 0, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 4278 then
(if i.val < 4277 then
[0, 3, 0, 2, 2, 1, 0, 3, 2]
else
[0, 3, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 4279 then
[0, 3, 0, 2, 2, 1, 1, 3, 3]
else
[0, 3, 0, 2, 2, 3, 0, 1, 2])))
else
(if i.val < 4284 then
(if i.val < 4282 then
(if i.val < 4281 then
[0, 3, 0, 2, 3, 3, 0, 1, 2]
else
[0, 3, 0, 2, 3, 3, 2, 1, 1])
else
(if i.val < 4283 then
[0, 3, 2, 1, 0, 0, 1, 2, 3]
else
[0, 3, 2, 1, 0, 3, 2, 1, 1]))
else
(if i.val < 4286 then
(if i.val < 4285 then
[0, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 3, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 4287 then
[0, 3, 2, 1, 1, 0, 3, 3, 0]
else
[0, 3, 2, 1, 1, 2, 3, 0, 1]))))))
else
(if i.val < 4320 then
(if i.val < 4304 then
(if i.val < 4296 then
(if i.val < 4292 then
(if i.val < 4290 then
(if i.val < 4289 then
[0, 3, 2, 2, 1, 0, 0, 3, 0]
else
[0, 3, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 4291 then
[0, 3, 2, 2, 1, 0, 3, 3, 0]
else
[0, 3, 2, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 4294 then
(if i.val < 4293 then
[0, 3, 2, 2, 1, 3, 0, 0, 1]
else
[0, 3, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 4295 then
[0, 3, 2, 2, 3, 0, 0, 1, 1]
else
[0, 3, 2, 2, 3, 0, 1, 2, 3])))
else
(if i.val < 4300 then
(if i.val < 4298 then
(if i.val < 4297 then
[0, 3, 3, 0, 0, 1, 2, 1, 3]
else
[0, 3, 3, 0, 0, 1, 2, 3, 0])
else
(if i.val < 4299 then
[0, 3, 3, 0, 0, 1, 2, 3, 3]
else
[0, 3, 3, 0, 0, 2, 1, 0, 0]))
else
(if i.val < 4302 then
(if i.val < 4301 then
[0, 3, 3, 0, 0, 2, 1, 1, 3]
else
[0, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 4303 then
[0, 3, 3, 0, 1, 1, 0, 2, 1]
else
[0, 3, 3, 0, 1, 1, 0, 2, 2]))))
else
(if i.val < 4312 then
(if i.val < 4308 then
(if i.val < 4306 then
(if i.val < 4305 then
[0, 3, 3, 0, 1, 1, 0, 3, 3]
else
[0, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 4307 then
[0, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 3, 3, 0, 2, 1, 0, 3, 2]))
else
(if i.val < 4310 then
(if i.val < 4309 then
[0, 3, 3, 0, 2, 1, 1, 0, 0]
else
[0, 3, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 4311 then
[0, 3, 3, 2, 1, 0, 0, 3, 3]
else
[0, 3, 3, 2, 1, 1, 0, 3, 3])))
else
(if i.val < 4316 then
(if i.val < 4314 then
(if i.val < 4313 then
[0, 3, 3, 2, 2, 1, 0, 3, 2]
else
[1, 0, 0, 1, 2, 1, 0, 3, 2])
else
(if i.val < 4315 then
[1, 0, 0, 1, 2, 1, 1, 2, 3]
else
[1, 0, 0, 1, 2, 1, 3, 0, 0]))
else
(if i.val < 4318 then
(if i.val < 4317 then
[1, 0, 0, 1, 2, 1, 3, 0, 1]
else
[1, 0, 0, 1, 2, 1, 3, 3, 2])
else
(if i.val < 4319 then
[1, 0, 0, 1, 2, 2, 1, 0, 3]
else
[1, 0, 0, 1, 2, 2, 1, 1, 3])))))
else
(if i.val < 4336 then
(if i.val < 4328 then
(if i.val < 4324 then
(if i.val < 4322 then
(if i.val < 4321 then
[1, 0, 0, 1, 2, 2, 1, 3, 2]
else
[1, 0, 0, 1, 2, 2, 1, 3, 3])
else
(if i.val < 4323 then
[1, 0, 0, 1, 2, 2, 3, 0, 0]
else
[1, 0, 0, 1, 2, 2, 3, 0, 1]))
else
(if i.val < 4326 then
(if i.val < 4325 then
[1, 0, 0, 1, 2, 2, 3, 2, 2]
else
[1, 0, 0, 1, 2, 2, 3, 3, 2])
else
(if i.val < 4327 then
[1, 0, 0, 1, 2, 3, 0, 0, 3]
else
[1, 0, 0, 1, 2, 3, 0, 2, 1])))
else
(if i.val < 4332 then
(if i.val < 4330 then
(if i.val < 4329 then
[1, 0, 0, 1, 2, 3, 0, 2, 2]
else
[1, 0, 0, 1, 2, 3, 3, 0, 1])
else
(if i.val < 4331 then
[1, 0, 0, 1, 3, 0, 0, 2, 1]
else
[1, 0, 0, 1, 3, 0, 0, 2, 2]))
else
(if i.val < 4334 then
(if i.val < 4333 then
[1, 0, 0, 1, 3, 0, 0, 3, 2]
else
[1, 0, 0, 1, 3, 0, 1, 2, 1])
else
(if i.val < 4335 then
[1, 0, 0, 1, 3, 0, 1, 2, 2]
else
[1, 0, 0, 1, 3, 0, 2, 2, 1]))))
else
(if i.val < 4344 then
(if i.val < 4340 then
(if i.val < 4338 then
(if i.val < 4337 then
[1, 0, 0, 1, 3, 2, 2, 1, 3]
else
[1, 0, 0, 1, 3, 3, 0, 2, 1])
else
(if i.val < 4339 then
[1, 0, 0, 1, 3, 3, 0, 2, 2]
else
[1, 0, 0, 1, 3, 3, 2, 2, 1]))
else
(if i.val < 4342 then
(if i.val < 4341 then
[1, 0, 0, 2, 1, 0, 0, 1, 3]
else
[1, 0, 0, 2, 1, 0, 0, 3, 0])
else
(if i.val < 4343 then
[1, 0, 0, 2, 1, 0, 3, 0, 0]
else
[1, 0, 0, 2, 1, 1, 2, 3, 2])))
else
(if i.val < 4348 then
(if i.val < 4346 then
(if i.val < 4345 then
[1, 0, 0, 2, 1, 3, 2, 2, 1]
else
[1, 0, 0, 2, 1, 3, 3, 0, 0])
else
(if i.val < 4347 then
[1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[1, 0, 0, 2, 2, 1, 3, 3, 2]))
else
(if i.val < 4350 then
(if i.val < 4349 then
[1, 0, 0, 2, 2, 3, 3, 0, 0]
else
[1, 0, 0, 2, 2, 3, 3, 2, 2])
else
(if i.val < 4351 then
[1, 0, 0, 2, 3, 0, 0, 1, 1]
else
[1, 0, 0, 2, 3, 0, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0034 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4416 then
(if i.val < 4384 then
(if i.val < 4368 then
(if i.val < 4360 then
(if i.val < 4356 then
(if i.val < 4354 then
(if i.val < 4353 then
[1, 0, 0, 2, 3, 0, 0, 2, 2]
else
[1, 0, 0, 2, 3, 2, 2, 3, 0])
else
(if i.val < 4355 then
[1, 0, 0, 2, 3, 3, 0, 1, 2]
else
[1, 0, 0, 2, 3, 3, 0, 2, 1]))
else
(if i.val < 4358 then
(if i.val < 4357 then
[1, 0, 0, 2, 3, 3, 0, 2, 2]
else
[1, 0, 0, 3, 0, 0, 1, 1, 3])
else
(if i.val < 4359 then
[1, 0, 0, 3, 0, 0, 2, 1, 1]
else
[1, 0, 0, 3, 0, 0, 2, 2, 1])))
else
(if i.val < 4364 then
(if i.val < 4362 then
(if i.val < 4361 then
[1, 0, 0, 3, 0, 0, 2, 3, 3]
else
[1, 0, 0, 3, 0, 0, 3, 2, 1])
else
(if i.val < 4363 then
[1, 0, 0, 3, 0, 0, 3, 2, 2]
else
[1, 0, 0, 3, 0, 1, 1, 0, 3]))
else
(if i.val < 4366 then
(if i.val < 4365 then
[1, 0, 0, 3, 0, 1, 2, 1, 1]
else
[1, 0, 0, 3, 0, 1, 2, 2, 1])
else
(if i.val < 4367 then
[1, 0, 0, 3, 0, 2, 1, 0, 3]
else
[1, 0, 0, 3, 0, 2, 3, 3, 0]))))
else
(if i.val < 4376 then
(if i.val < 4372 then
(if i.val < 4370 then
(if i.val < 4369 then
[1, 0, 0, 3, 2, 2, 1, 1, 3]
else
[1, 0, 0, 3, 2, 2, 3, 0, 1])
else
(if i.val < 4371 then
[1, 0, 0, 3, 3, 0, 0, 2, 1]
else
[1, 0, 0, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 4374 then
(if i.val < 4373 then
[1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[1, 0, 0, 3, 3, 0, 2, 2, 1])
else
(if i.val < 4375 then
[1, 0, 0, 3, 3, 0, 2, 2, 3]
else
[1, 0, 0, 3, 3, 0, 2, 3, 3])))
else
(if i.val < 4380 then
(if i.val < 4378 then
(if i.val < 4377 then
[1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[1, 0, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 4379 then
[1, 0, 2, 1, 1, 0, 0, 2, 1]
else
[1, 0, 2, 1, 1, 0, 0, 3, 0]))
else
(if i.val < 4382 then
(if i.val < 4381 then
[1, 0, 2, 1, 1, 0, 2, 1, 3]
else
[1, 0, 2, 1, 1, 0, 3, 0, 0])
else
(if i.val < 4383 then
[1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[1, 0, 2, 1, 1, 2, 3, 0, 1])))))
else
(if i.val < 4400 then
(if i.val < 4392 then
(if i.val < 4388 then
(if i.val < 4386 then
(if i.val < 4385 then
[1, 0, 2, 1, 1, 3, 2, 1, 1]
else
[1, 0, 2, 1, 1, 3, 2, 2, 3])
else
(if i.val < 4387 then
[1, 0, 2, 2, 1, 0, 0, 3, 3]
else
[1, 0, 2, 2, 1, 1, 0, 3, 2]))
else
(if i.val < 4390 then
(if i.val < 4389 then
[1, 0, 2, 2, 1, 1, 3, 0, 0]
else
[1, 0, 2, 2, 1, 3, 2, 2, 1])
else
(if i.val < 4391 then
[1, 0, 2, 2, 1, 3, 2, 2, 3]
else
[1, 0, 2, 2, 1, 3, 3, 0, 0])))
else
(if i.val < 4396 then
(if i.val < 4394 then
(if i.val < 4393 then
[1, 0, 2, 2, 1, 3, 3, 2, 1]
else
[1, 0, 2, 2, 3, 0, 0, 2, 2])
else
(if i.val < 4395 then
[1, 0, 2, 2, 3, 0, 1, 2, 2]
else
[1, 0, 2, 2, 3, 0, 1, 2, 3]))
else
(if i.val < 4398 then
(if i.val < 4397 then
[1, 0, 2, 2, 3, 2, 1, 0, 0]
else
[1, 0, 2, 2, 3, 2, 1, 0, 3])
else
(if i.val < 4399 then
[1, 0, 2, 2, 3, 2, 2, 1, 3]
else
[1, 0, 2, 2, 3, 3, 0, 2, 3]))))
else
(if i.val < 4408 then
(if i.val < 4404 then
(if i.val < 4402 then
(if i.val < 4401 then
[1, 0, 2, 3, 0, 0, 2, 3, 2]
else
[1, 0, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 4403 then
[1, 0, 2, 3, 0, 1, 1, 2, 1]
else
[1, 0, 2, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 4406 then
(if i.val < 4405 then
[1, 0, 2, 3, 0, 2, 1, 0, 3]
else
[1, 0, 2, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4407 then
[1, 0, 2, 3, 0, 2, 2, 3, 3]
else
[1, 0, 2, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 4412 then
(if i.val < 4410 then
(if i.val < 4409 then
[1, 0, 2, 3, 2, 1, 0, 0, 3]
else
[1, 0, 2, 3, 2, 1, 0, 3, 2])
else
(if i.val < 4411 then
[1, 0, 2, 3, 2, 1, 0, 3, 3]
else
[1, 0, 2, 3, 2, 2, 3, 0, 0]))
else
(if i.val < 4414 then
(if i.val < 4413 then
[1, 0, 2, 3, 3, 0, 0, 2, 1]
else
[1, 0, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 4415 then
[1, 0, 2, 3, 3, 0, 1, 2, 1]
else
[1, 0, 2, 3, 3, 0, 1, 2, 2]))))))
else
(if i.val < 4448 then
(if i.val < 4432 then
(if i.val < 4424 then
(if i.val < 4420 then
(if i.val < 4418 then
(if i.val < 4417 then
[1, 0, 2, 3, 3, 2, 1, 0, 0]
else
[1, 0, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 4419 then
[1, 0, 3, 0, 0, 1, 1, 2, 1]
else
[1, 0, 3, 0, 0, 1, 3, 2, 1]))
else
(if i.val < 4422 then
(if i.val < 4421 then
[1, 0, 3, 0, 0, 2, 1, 1, 3]
else
[1, 0, 3, 0, 0, 2, 2, 1, 1])
else
(if i.val < 4423 then
[1, 0, 3, 0, 0, 2, 2, 3, 0]
else
[1, 0, 3, 0, 0, 3, 2, 1, 1])))
else
(if i.val < 4428 then
(if i.val < 4426 then
(if i.val < 4425 then
[1, 0, 3, 0, 0, 3, 2, 2, 1]
else
[1, 0, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 4427 then
[1, 0, 3, 0, 1, 1, 0, 2, 2]
else
[1, 0, 3, 0, 1, 2, 1, 1, 3]))
else
(if i.val < 4430 then
(if i.val < 4429 then
[1, 0, 3, 0, 1, 2, 2, 3, 0]
else
[1, 0, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 4431 then
[1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[1, 0, 3, 0, 2, 1, 1, 0, 0]))))
else
(if i.val < 4440 then
(if i.val < 4436 then
(if i.val < 4434 then
(if i.val < 4433 then
[1, 0, 3, 0, 2, 2, 1, 0, 3]
else
[1, 0, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 4435 then
[1, 0, 3, 0, 2, 2, 3, 0, 1]
else
[1, 0, 3, 0, 2, 3, 3, 0, 1]))
else
(if i.val < 4438 then
(if i.val < 4437 then
[1, 0, 3, 2, 1, 1, 0, 0, 3]
else
[1, 0, 3, 2, 2, 1, 0, 3, 0])
else
(if i.val < 4439 then
[1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[1, 0, 3, 3, 0, 2, 2, 3, 3])))
else
(if i.val < 4444 then
(if i.val < 4442 then
(if i.val < 4441 then
[1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[1, 0, 3, 3, 2, 1, 0, 3, 2])
else
(if i.val < 4443 then
[1, 1, 0, 0, 2, 1, 1, 2, 3]
else
[1, 1, 0, 0, 2, 1, 3, 0, 1]))
else
(if i.val < 4446 then
(if i.val < 4445 then
[1, 1, 0, 0, 2, 1, 3, 3, 2]
else
[1, 1, 0, 0, 2, 2, 1, 0, 3])
else
(if i.val < 4447 then
[1, 1, 0, 0, 2, 2, 1, 3, 2]
else
[1, 1, 0, 0, 2, 2, 1, 3, 3])))))
else
(if i.val < 4464 then
(if i.val < 4456 then
(if i.val < 4452 then
(if i.val < 4450 then
(if i.val < 4449 then
[1, 1, 0, 0, 2, 2, 3, 3, 2]
else
[1, 1, 0, 0, 2, 3, 0, 2, 2])
else
(if i.val < 4451 then
[1, 1, 0, 0, 3, 0, 0, 2, 2]
else
[1, 1, 0, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 4454 then
(if i.val < 4453 then
[1, 1, 0, 0, 3, 3, 0, 2, 1]
else
[1, 1, 0, 0, 3, 3, 2, 1, 1])
else
(if i.val < 4455 then
[1, 1, 0, 2, 1, 3, 0, 0, 3]
else
[1, 1, 0, 2, 1, 3, 2, 2, 3])))
else
(if i.val < 4460 then
(if i.val < 4458 then
(if i.val < 4457 then
[1, 1, 0, 2, 2, 1, 0, 0, 3]
else
[1, 1, 0, 2, 2, 1, 0, 3, 0])
else
(if i.val < 4459 then
[1, 1, 0, 2, 2, 1, 0, 3, 2]
else
[1, 1, 0, 2, 2, 1, 1, 3, 2]))
else
(if i.val < 4462 then
(if i.val < 4461 then
[1, 1, 0, 2, 2, 1, 3, 0, 1]
else
[1, 1, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 4463 then
[1, 1, 0, 2, 2, 3, 0, 1, 2]
else
[1, 1, 0, 2, 2, 3, 2, 2, 1]))))
else
(if i.val < 4472 then
(if i.val < 4468 then
(if i.val < 4466 then
(if i.val < 4465 then
[1, 1, 0, 2, 2, 3, 2, 2, 3]
else
[1, 1, 0, 2, 2, 3, 3, 2, 2])
else
(if i.val < 4467 then
[1, 1, 0, 2, 3, 0, 1, 2, 1]
else
[1, 1, 0, 2, 3, 0, 2, 1, 3]))
else
(if i.val < 4470 then
(if i.val < 4469 then
[1, 1, 0, 2, 3, 3, 0, 1, 2]
else
[1, 1, 0, 2, 3, 3, 0, 2, 2])
else
(if i.val < 4471 then
[1, 1, 0, 3, 0, 0, 1, 1, 3]
else
[1, 1, 0, 3, 0, 0, 2, 1, 1])))
else
(if i.val < 4476 then
(if i.val < 4474 then
(if i.val < 4473 then
[1, 1, 0, 3, 0, 0, 2, 2, 1]
else
[1, 1, 0, 3, 0, 0, 3, 2, 1])
else
(if i.val < 4475 then
[1, 1, 0, 3, 0, 1, 2, 3, 0]
else
[1, 1, 0, 3, 0, 1, 2, 3, 3]))
else
(if i.val < 4478 then
(if i.val < 4477 then
[1, 1, 0, 3, 0, 2, 1, 0, 3]
else
[1, 1, 0, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4479 then
[1, 1, 0, 3, 0, 2, 2, 3, 3]
else
[1, 1, 0, 3, 2, 2, 1, 1, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0035 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4544 then
(if i.val < 4512 then
(if i.val < 4496 then
(if i.val < 4488 then
(if i.val < 4484 then
(if i.val < 4482 then
(if i.val < 4481 then
[1, 1, 0, 3, 3, 0, 1, 2, 1]
else
[1, 1, 2, 1, 0, 3, 0, 1, 2])
else
(if i.val < 4483 then
[1, 1, 2, 1, 0, 3, 0, 2, 1]
else
[1, 1, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 4486 then
(if i.val < 4485 then
[1, 1, 2, 1, 1, 0, 0, 3, 0]
else
[1, 1, 2, 1, 1, 0, 0, 3, 3])
else
(if i.val < 4487 then
[1, 1, 2, 1, 1, 0, 2, 1, 3]
else
[1, 1, 2, 1, 1, 2, 3, 0, 0])))
else
(if i.val < 4492 then
(if i.val < 4490 then
(if i.val < 4489 then
[1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[1, 1, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 4491 then
[1, 1, 2, 1, 1, 3, 2, 2, 3]
else
[1, 1, 2, 1, 1, 3, 3, 2, 2]))
else
(if i.val < 4494 then
(if i.val < 4493 then
[1, 1, 2, 1, 3, 0, 0, 3, 2]
else
[1, 1, 2, 1, 3, 0, 1, 2, 2])
else
(if i.val < 4495 then
[1, 1, 2, 1, 3, 0, 2, 2, 3]
else
[1, 1, 2, 1, 3, 2, 2, 1, 1]))))
else
(if i.val < 4504 then
(if i.val < 4500 then
(if i.val < 4498 then
(if i.val < 4497 then
[1, 1, 2, 2, 1, 1, 3, 0, 0]
else
[1, 1, 2, 2, 1, 3, 2, 1, 1])
else
(if i.val < 4499 then
[1, 1, 2, 2, 3, 0, 1, 2, 3]
else
[1, 1, 2, 2, 3, 2, 2, 1, 1]))
else
(if i.val < 4502 then
(if i.val < 4501 then
[1, 1, 2, 2, 3, 3, 0, 2, 3]
else
[1, 1, 2, 3, 0, 0, 3, 2, 2])
else
(if i.val < 4503 then
[1, 1, 2, 3, 0, 1, 1, 2, 2]
else
[1, 1, 2, 3, 0, 1, 2, 2, 1])))
else
(if i.val < 4508 then
(if i.val < 4506 then
(if i.val < 4505 then
[1, 1, 2, 3, 0, 2, 1, 1, 3]
else
[1, 1, 2, 3, 2, 1, 0, 0, 3])
else
(if i.val < 4507 then
[1, 1, 2, 3, 3, 0, 0, 1, 1]
else
[1, 1, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 4510 then
(if i.val < 4509 then
[1, 1, 2, 3, 3, 0, 1, 2, 1]
else
[1, 1, 2, 3, 3, 0, 2, 3, 3])
else
(if i.val < 4511 then
[1, 1, 2, 3, 3, 2, 1, 0, 0]
else
[1, 1, 2, 3, 3, 2, 1, 0, 3])))))
else
(if i.val < 4528 then
(if i.val < 4520 then
(if i.val < 4516 then
(if i.val < 4514 then
(if i.val < 4513 then
[1, 1, 3, 0, 0, 1, 3, 2, 1]
else
[1, 1, 3, 0, 0, 3, 2, 1, 1])
else
(if i.val < 4515 then
[1, 1, 3, 0, 0, 3, 2, 2, 1]
else
[1, 1, 3, 0, 1, 1, 0, 2, 1]))
else
(if i.val < 4518 then
(if i.val < 4517 then
[1, 1, 3, 0, 1, 1, 0, 2, 2]
else
[1, 1, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 4519 then
[1, 1, 3, 0, 1, 2, 3, 0, 0]
else
[1, 1, 3, 0, 1, 2, 3, 3, 0])))
else
(if i.val < 4524 then
(if i.val < 4522 then
(if i.val < 4521 then
[1, 1, 3, 0, 1, 2, 3, 3, 2]
else
[1, 1, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 4523 then
[1, 1, 3, 0, 2, 2, 1, 0, 3]
else
[1, 1, 3, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 4526 then
(if i.val < 4525 then
[1, 1, 3, 0, 2, 2, 3, 0, 1]
else
[1, 1, 3, 2, 2, 1, 1, 3, 2])
else
(if i.val < 4527 then
[1, 1, 3, 3, 0, 1, 2, 2, 3]
else
[1, 1, 3, 3, 0, 1, 2, 3, 0]))))
else
(if i.val < 4536 then
(if i.val < 4532 then
(if i.val < 4530 then
(if i.val < 4529 then
[1, 1, 3, 3, 0, 2, 3, 3, 2]
else
[1, 2, 1, 0, 0, 1, 3, 0, 0])
else
(if i.val < 4531 then
[1, 2, 1, 0, 0, 1, 3, 3, 2]
else
[1, 2, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 4534 then
(if i.val < 4533 then
[1, 2, 1, 0, 3, 2, 1, 0, 0]
else
[1, 2, 1, 0, 3, 2, 1, 0, 3])
else
(if i.val < 4535 then
[1, 2, 1, 0, 3, 2, 2, 3, 0]
else
[1, 2, 1, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 4540 then
(if i.val < 4538 then
(if i.val < 4537 then
[1, 2, 1, 1, 0, 0, 3, 0, 0]
else
[1, 2, 1, 1, 0, 0, 3, 0, 1])
else
(if i.val < 4539 then
[1, 2, 1, 1, 0, 2, 1, 3, 2]
else
[1, 2, 1, 1, 0, 2, 1, 3, 3]))
else
(if i.val < 4542 then
(if i.val < 4541 then
[1, 2, 1, 1, 0, 2, 3, 3, 2]
else
[1, 2, 1, 1, 2, 3, 2, 2, 3])
else
(if i.val < 4543 then
[1, 2, 1, 1, 3, 0, 1, 2, 2]
else
[1, 2, 1, 1, 3, 0, 1, 2, 3]))))))
else
(if i.val < 4576 then
(if i.val < 4560 then
(if i.val < 4552 then
(if i.val < 4548 then
(if i.val < 4546 then
(if i.val < 4545 then
[1, 2, 1, 3, 0, 0, 1, 2, 3]
else
[1, 2, 1, 3, 0, 0, 2, 2, 1])
else
(if i.val < 4547 then
[1, 2, 1, 3, 0, 0, 2, 2, 3]
else
[1, 2, 1, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 4550 then
(if i.val < 4549 then
[1, 2, 1, 3, 0, 0, 3, 2, 2]
else
[1, 2, 1, 3, 0, 2, 2, 3, 3])
else
(if i.val < 4551 then
[1, 2, 1, 3, 2, 2, 1, 1, 3]
else
[1, 2, 1, 3, 2, 2, 3, 0, 0])))
else
(if i.val < 4556 then
(if i.val < 4554 then
(if i.val < 4553 then
[1, 2, 1, 3, 3, 0, 0, 2, 1]
else
[1, 2, 1, 3, 3, 0, 1, 2, 3])
else
(if i.val < 4555 then
[1, 2, 1, 3, 3, 0, 2, 1, 3]
else
[1, 2, 1, 3, 3, 0, 2, 2, 3]))
else
(if i.val < 4558 then
(if i.val < 4557 then
[1, 2, 1, 3, 3, 0, 2, 3, 3]
else
[1, 2, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 4559 then
[1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[1, 2, 2, 1, 0, 0, 3, 3, 2]))))
else
(if i.val < 4568 then
(if i.val < 4564 then
(if i.val < 4562 then
(if i.val < 4561 then
[1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[1, 2, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 4563 then
[1, 2, 2, 1, 0, 3, 2, 1, 1]
else
[1, 2, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 4566 then
(if i.val < 4565 then
[1, 2, 2, 1, 1, 3, 0, 1, 2]
else
[1, 2, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 4567 then
[1, 2, 2, 1, 3, 0, 0, 2, 1]
else
[1, 2, 2, 3, 0, 0, 2, 2, 1])))
else
(if i.val < 4572 then
(if i.val < 4570 then
(if i.val < 4569 then
[1, 2, 2, 3, 2, 1, 0, 3, 3]
else
[1, 2, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 4571 then
[1, 2, 3, 0, 0, 1, 2, 1, 3]
else
[1, 2, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 4574 then
(if i.val < 4573 then
[1, 2, 3, 0, 0, 1, 2, 3, 2]
else
[1, 2, 3, 0, 0, 1, 3, 0, 0])
else
(if i.val < 4575 then
[1, 2, 3, 0, 0, 2, 2, 1, 1]
else
[1, 2, 3, 0, 0, 2, 3, 3, 2])))))
else
(if i.val < 4592 then
(if i.val < 4584 then
(if i.val < 4580 then
(if i.val < 4578 then
(if i.val < 4577 then
[1, 2, 3, 0, 1, 1, 0, 2, 1]
else
[1, 2, 3, 0, 1, 1, 0, 2, 2])
else
(if i.val < 4579 then
[1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[1, 2, 3, 0, 1, 2, 1, 1, 3]))
else
(if i.val < 4582 then
(if i.val < 4581 then
[1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[1, 2, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 4583 then
[1, 2, 3, 0, 1, 2, 3, 3, 2]
else
[1, 2, 3, 0, 2, 2, 1, 1, 3])))
else
(if i.val < 4588 then
(if i.val < 4586 then
(if i.val < 4585 then
[1, 2, 3, 2, 1, 0, 3, 3, 0]
else
[1, 2, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 4587 then
[1, 2, 3, 3, 0, 0, 1, 2, 1]
else
[1, 2, 3, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 4590 then
(if i.val < 4589 then
[1, 2, 3, 3, 0, 1, 2, 3, 0]
else
[1, 2, 3, 3, 0, 2, 1, 1, 3])
else
(if i.val < 4591 then
[1, 2, 3, 3, 2, 1, 1, 2, 3]
else
[1, 3, 0, 0, 1, 1, 2, 1, 3]))))
else
(if i.val < 4600 then
(if i.val < 4596 then
(if i.val < 4594 then
(if i.val < 4593 then
[1, 3, 0, 0, 1, 2, 1, 1, 3]
else
[1, 3, 0, 0, 1, 2, 1, 3, 0])
else
(if i.val < 4595 then
[1, 3, 0, 0, 2, 2, 1, 0, 0]
else
[1, 3, 0, 0, 2, 2, 3, 3, 2]))
else
(if i.val < 4598 then
(if i.val < 4597 then
[1, 3, 0, 0, 3, 2, 2, 3, 0]
else
[1, 3, 0, 1, 1, 0, 2, 2, 3])
else
(if i.val < 4599 then
[1, 3, 0, 1, 1, 0, 3, 3, 0]
else
[1, 3, 0, 1, 1, 0, 3, 3, 2])))
else
(if i.val < 4604 then
(if i.val < 4602 then
(if i.val < 4601 then
[1, 3, 0, 1, 1, 2, 2, 3, 0]
else
[1, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 4603 then
[1, 3, 0, 1, 2, 2, 1, 0, 0]
else
[1, 3, 0, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 4606 then
(if i.val < 4605 then
[1, 3, 0, 2, 3, 3, 0, 1, 2]
else
[1, 3, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 4607 then
[1, 3, 2, 1, 0, 3, 2, 2, 3]
else
[1, 3, 2, 1, 1, 0, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0036 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4672 then
(if i.val < 4640 then
(if i.val < 4624 then
(if i.val < 4616 then
(if i.val < 4612 then
(if i.val < 4610 then
(if i.val < 4609 then
[1, 3, 2, 2, 1, 0, 0, 3, 0]
else
[1, 3, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 4611 then
[1, 3, 2, 2, 1, 3, 0, 0, 1]
else
[1, 3, 2, 2, 1, 3, 0, 2, 1]))
else
(if i.val < 4614 then
(if i.val < 4613 then
[1, 3, 2, 2, 3, 0, 1, 2, 3]
else
[1, 3, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 4615 then
[1, 3, 3, 0, 0, 1, 2, 3, 0]
else
[1, 3, 3, 0, 0, 2, 3, 3, 2])))
else
(if i.val < 4620 then
(if i.val < 4618 then
(if i.val < 4617 then
[1, 3, 3, 0, 1, 1, 0, 2, 1]
else
[1, 3, 3, 0, 1, 1, 0, 2, 2])
else
(if i.val < 4619 then
[1, 3, 3, 0, 1, 2, 3, 0, 0]
else
[1, 3, 3, 0, 2, 1, 0, 3, 2]))
else
(if i.val < 4622 then
(if i.val < 4621 then
[1, 3, 3, 0, 2, 1, 1, 0, 0]
else
[1, 3, 3, 0, 2, 1, 1, 2, 3])
else
(if i.val < 4623 then
[2, 1, 0, 0, 1, 2, 2, 3, 2]
else
[2, 1, 0, 0, 1, 2, 3, 0, 0]))))
else
(if i.val < 4632 then
(if i.val < 4628 then
(if i.val < 4626 then
(if i.val < 4625 then
[2, 1, 0, 0, 1, 2, 3, 0, 1]
else
[2, 1, 0, 0, 1, 2, 3, 3, 0])
else
(if i.val < 4627 then
[2, 1, 0, 0, 1, 3, 2, 1, 1]
else
[2, 1, 0, 0, 1, 3, 2, 2, 1]))
else
(if i.val < 4630 then
(if i.val < 4629 then
[2, 1, 0, 0, 3, 3, 2, 2, 1]
else
[2, 1, 0, 3, 0, 0, 1, 2, 1])
else
(if i.val < 4631 then
[2, 1, 0, 3, 0, 2, 1, 0, 3]
else
[2, 1, 0, 3, 0, 2, 2, 1, 3])))
else
(if i.val < 4636 then
(if i.val < 4634 then
(if i.val < 4633 then
[2, 1, 0, 3, 2, 1, 1, 0, 0]
else
[2, 1, 0, 3, 2, 2, 1, 0, 3])
else
(if i.val < 4635 then
[2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[2, 1, 0, 3, 2, 2, 1, 3, 2]))
else
(if i.val < 4638 then
(if i.val < 4637 then
[2, 1, 0, 3, 3, 0, 2, 2, 3]
else
[2, 1, 0, 3, 3, 2, 1, 0, 3])
else
(if i.val < 4639 then
[2, 1, 1, 0, 0, 2, 1, 1, 3]
else
[2, 1, 1, 0, 0, 3, 3, 2, 2])))))
else
(if i.val < 4656 then
(if i.val < 4648 then
(if i.val < 4644 then
(if i.val < 4642 then
(if i.val < 4641 then
[2, 1, 1, 0, 2, 3, 0, 2, 1]
else
[2, 1, 1, 0, 2, 3, 2, 2, 3])
else
(if i.val < 4643 then
[2, 1, 1, 0, 3, 0, 1, 2, 1]
else
[2, 1, 1, 0, 3, 2, 2, 3, 0]))
else
(if i.val < 4646 then
(if i.val < 4645 then
[2, 1, 1, 2, 3, 0, 0, 2, 2]
else
[2, 1, 1, 2, 3, 0, 1, 2, 2])
else
(if i.val < 4647 then
[2, 1, 1, 2, 3, 0, 2, 2, 1]
else
[2, 1, 1, 2, 3, 3, 0, 2, 3])))
else
(if i.val < 4652 then
(if i.val < 4650 then
(if i.val < 4649 then
[2, 1, 1, 3, 0, 0, 1, 2, 1]
else
[2, 1, 1, 3, 0, 0, 2, 2, 1])
else
(if i.val < 4651 then
[2, 1, 1, 3, 0, 0, 3, 2, 1]
else
[2, 1, 1, 3, 0, 1, 2, 2, 3]))
else
(if i.val < 4654 then
(if i.val < 4653 then
[2, 1, 1, 3, 0, 2, 1, 0, 3]
else
[2, 1, 1, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4655 then
[2, 1, 1, 3, 3, 0, 0, 2, 1]
else
[2, 1, 3, 0, 0, 1, 2, 1, 3]))))
else
(if i.val < 4664 then
(if i.val < 4660 then
(if i.val < 4658 then
(if i.val < 4657 then
[2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[2, 1, 3, 0, 1, 2, 2, 1, 3])
else
(if i.val < 4659 then
[2, 1, 3, 0, 1, 2, 3, 0, 0]
else
[2, 1, 3, 0, 2, 2, 3, 0, 1]))
else
(if i.val < 4662 then
(if i.val < 4661 then
[2, 1, 3, 2, 1, 0, 3, 3, 0]
else
[2, 1, 3, 3, 0, 0, 1, 2, 1])
else
(if i.val < 4663 then
[2, 2, 1, 0, 0, 3, 2, 2, 1]
else
[2, 2, 1, 0, 3, 0, 1, 2, 1])))
else
(if i.val < 4668 then
(if i.val < 4666 then
(if i.val < 4665 then
[2, 2, 1, 0, 3, 0, 2, 2, 1]
else
[2, 2, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 4667 then
[2, 2, 1, 1, 0, 3, 0, 1, 2]
else
[2, 2, 1, 3, 0, 0, 1, 2, 1]))
else
(if i.val < 4670 then
(if i.val < 4669 then
[2, 2, 1, 3, 0, 0, 3, 2, 1]
else
[2, 2, 1, 3, 2, 2, 1, 3, 2])
else
(if i.val < 4671 then
[2, 2, 1, 3, 3, 0, 1, 2, 3]
else
[2, 2, 1, 3, 3, 0, 2, 3, 3]))))))
else
(if i.val < 4704 then
(if i.val < 4688 then
(if i.val < 4680 then
(if i.val < 4676 then
(if i.val < 4674 then
(if i.val < 4673 then
[2, 2, 3, 0, 0, 2, 1, 1, 3]
else
[2, 2, 3, 0, 0, 2, 2, 1, 1])
else
(if i.val < 4675 then
[2, 2, 3, 0, 1, 1, 0, 2, 1]
else
[2, 2, 3, 0, 1, 1, 0, 3, 3]))
else
(if i.val < 4678 then
(if i.val < 4677 then
[2, 2, 3, 0, 1, 2, 3, 0, 0]
else
[2, 2, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 4679 then
[2, 2, 3, 0, 2, 2, 1, 1, 3]
else
[2, 2, 3, 2, 1, 0, 3, 3, 0])))
else
(if i.val < 4684 then
(if i.val < 4682 then
(if i.val < 4681 then
[2, 2, 3, 2, 2, 1, 1, 3, 2]
else
[2, 3, 0, 0, 3, 2, 1, 0, 0])
else
(if i.val < 4683 then
[2, 3, 0, 1, 1, 0, 3, 3, 2]
else
[2, 3, 0, 1, 2, 1, 1, 0, 3]))
else
(if i.val < 4686 then
(if i.val < 4685 then
[2, 3, 0, 1, 2, 2, 1, 0, 0]
else
[2, 3, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 4687 then
[2, 3, 0, 1, 2, 3, 3, 0, 0]
else
[2, 3, 0, 1, 2, 3, 3, 0, 1]))))
else
(if i.val < 4696 then
(if i.val < 4692 then
(if i.val < 4690 then
(if i.val < 4689 then
[2, 3, 0, 2, 1, 1, 0, 3, 3]
else
[2, 3, 0, 2, 2, 1, 0, 0, 3])
else
(if i.val < 4691 then
[2, 3, 2, 1, 0, 0, 1, 2, 3]
else
[2, 3, 2, 1, 1, 0, 3, 3, 0]))
else
(if i.val < 4694 then
(if i.val < 4693 then
[2, 3, 2, 2, 3, 0, 0, 1, 1]
else
[2, 3, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 4695 then
[2, 3, 3, 0, 0, 2, 1, 1, 3]
else
[2, 3, 3, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 4700 then
(if i.val < 4698 then
(if i.val < 4697 then
[2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[2, 3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 4699 then
[3, 0, 0, 1, 1, 2, 3, 0, 1]
else
[3, 0, 0, 1, 2, 3, 0, 1, 2]))
else
(if i.val < 4702 then
(if i.val < 4701 then
[3, 0, 0, 1, 3, 0, 0, 2, 1]
else
[3, 0, 0, 2, 1, 0, 0, 3, 3])
else
(if i.val < 4703 then
[3, 0, 0, 2, 1, 0, 3, 0, 0]
else
[3, 0, 0, 2, 1, 3, 2, 2, 3])))))
else
(if i.val < 4720 then
(if i.val < 4712 then
(if i.val < 4708 then
(if i.val < 4706 then
(if i.val < 4705 then
[3, 0, 0, 2, 1, 3, 3, 0, 0]
else
[3, 0, 0, 2, 2, 1, 0, 3, 2])
else
(if i.val < 4707 then
[3, 0, 0, 2, 2, 1, 1, 3, 2]
else
[3, 0, 1, 1, 0, 2, 1, 3, 3]))
else
(if i.val < 4710 then
(if i.val < 4709 then
[3, 0, 1, 1, 0, 3, 2, 2, 1]
else
[3, 0, 1, 1, 0, 3, 3, 2, 2])
else
(if i.val < 4711 then
[3, 0, 1, 2, 1, 1, 0, 0, 3]
else
[3, 0, 1, 2, 1, 3, 3, 0, 0])))
else
(if i.val < 4716 then
(if i.val < 4714 then
(if i.val < 4713 then
[3, 0, 2, 1, 0, 3, 0, 0, 3]
else
[3, 0, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 4715 then
[3, 0, 2, 1, 1, 3, 3, 0, 1]
else
[3, 0, 2, 2, 1, 1, 3, 3, 2]))
else
(if i.val < 4718 then
(if i.val < 4717 then
[3, 0, 2, 3, 3, 0, 1, 2, 1]
else
[3, 0, 2, 3, 3, 0, 2, 1, 1])
else
(if i.val < 4719 then
[3, 2, 1, 0, 0, 1, 2, 2, 3]
else
[3, 2, 1, 0, 3, 2, 2, 1, 3]))))
else
(if i.val < 4728 then
(if i.val < 4724 then
(if i.val < 4722 then
(if i.val < 4721 then
[3, 2, 1, 0, 3, 2, 2, 3, 0]
else
[3, 2, 1, 1, 0, 2, 1, 1, 3])
else
(if i.val < 4723 then
[3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[3, 2, 2, 1, 0, 3, 2, 1, 1]))
else
(if i.val < 4726 then
(if i.val < 4725 then
[3, 2, 2, 1, 3, 0, 0, 2, 1]
else
[3, 2, 2, 1, 3, 0, 0, 2, 3])
else
(if i.val < 4727 then
[3, 3, 0, 1, 1, 2, 2, 3, 3]
else
[3, 3, 0, 2, 1, 3, 3, 0, 0])))
else
(if i.val < 4732 then
(if i.val < 4730 then
(if i.val < 4729 then
[3, 3, 2, 1, 0, 3, 2, 1, 1]
else
[3, 3, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 4731 then
[0, 0, 1, 0, 0, 1, 2, 1, 0, 3]
else
[0, 0, 1, 0, 0, 1, 2, 1, 1, 3]))
else
(if i.val < 4734 then
(if i.val < 4733 then
[0, 0, 1, 0, 0, 1, 2, 1, 3, 0]
else
[0, 0, 1, 0, 0, 1, 2, 1, 3, 3])
else
(if i.val < 4735 then
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0037 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4800 then
(if i.val < 4768 then
(if i.val < 4752 then
(if i.val < 4744 then
(if i.val < 4740 then
(if i.val < 4738 then
(if i.val < 4737 then
[0, 0, 1, 0, 0, 1, 2, 2, 3, 2]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3, 3])
else
(if i.val < 4739 then
[0, 0, 1, 0, 0, 1, 2, 3, 0, 0]
else
[0, 0, 1, 0, 0, 1, 2, 3, 0, 1]))
else
(if i.val < 4742 then
(if i.val < 4741 then
[0, 0, 1, 0, 0, 1, 2, 3, 2, 1]
else
[0, 0, 1, 0, 0, 1, 2, 3, 3, 0])
else
(if i.val < 4743 then
[0, 0, 1, 0, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 0, 0, 1, 3, 0, 0, 1])))
else
(if i.val < 4748 then
(if i.val < 4746 then
(if i.val < 4745 then
[0, 0, 1, 0, 0, 1, 3, 0, 0, 3]
else
[0, 0, 1, 0, 0, 1, 3, 0, 1, 2])
else
(if i.val < 4747 then
[0, 0, 1, 0, 0, 1, 3, 0, 2, 1]
else
[0, 0, 1, 0, 0, 1, 3, 2, 1, 1]))
else
(if i.val < 4750 then
(if i.val < 4749 then
[0, 0, 1, 0, 0, 1, 3, 2, 2, 1]
else
[0, 0, 1, 0, 0, 1, 3, 2, 2, 3])
else
(if i.val < 4751 then
[0, 0, 1, 0, 0, 1, 3, 3, 0, 1]
else
[0, 0, 1, 0, 0, 1, 3, 3, 2, 1]))))
else
(if i.val < 4760 then
(if i.val < 4756 then
(if i.val < 4754 then
(if i.val < 4753 then
[0, 0, 1, 0, 0, 1, 3, 3, 2, 2]
else
[0, 0, 1, 0, 0, 2, 1, 0, 0, 3])
else
(if i.val < 4755 then
[0, 0, 1, 0, 0, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3]))
else
(if i.val < 4758 then
(if i.val < 4757 then
[0, 0, 1, 0, 0, 2, 1, 3, 0, 0]
else
[0, 0, 1, 0, 0, 2, 1, 3, 0, 1])
else
(if i.val < 4759 then
[0, 0, 1, 0, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 0, 0, 2, 2, 1, 0, 3])))
else
(if i.val < 4764 then
(if i.val < 4762 then
(if i.val < 4761 then
[0, 0, 1, 0, 0, 2, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 2, 2, 1, 3, 2])
else
(if i.val < 4763 then
[0, 0, 1, 0, 0, 2, 2, 1, 3, 3]
else
[0, 0, 1, 0, 0, 2, 2, 3, 0, 0]))
else
(if i.val < 4766 then
(if i.val < 4765 then
[0, 0, 1, 0, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 0, 0, 2, 2, 3, 2, 2])
else
(if i.val < 4767 then
[0, 0, 1, 0, 0, 2, 2, 3, 3, 2]
else
[0, 0, 1, 0, 0, 2, 3, 0, 0, 1])))))
else
(if i.val < 4784 then
(if i.val < 4776 then
(if i.val < 4772 then
(if i.val < 4770 then
(if i.val < 4769 then
[0, 0, 1, 0, 0, 2, 3, 0, 0, 3]
else
[0, 0, 1, 0, 0, 2, 3, 0, 2, 1])
else
(if i.val < 4771 then
[0, 0, 1, 0, 0, 2, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 2, 3, 0, 2, 3]))
else
(if i.val < 4774 then
(if i.val < 4773 then
[0, 0, 1, 0, 0, 2, 3, 2, 1, 1]
else
[0, 0, 1, 0, 0, 2, 3, 3, 0, 0])
else
(if i.val < 4775 then
[0, 0, 1, 0, 0, 2, 3, 3, 0, 1]
else
[0, 0, 1, 0, 0, 3, 0, 0, 1, 3])))
else
(if i.val < 4780 then
(if i.val < 4778 then
(if i.val < 4777 then
[0, 0, 1, 0, 0, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 0, 3, 0, 0, 2, 2])
else
(if i.val < 4779 then
[0, 0, 1, 0, 0, 3, 0, 0, 2, 3]
else
[0, 0, 1, 0, 0, 3, 0, 0, 3, 2]))
else
(if i.val < 4782 then
(if i.val < 4781 then
[0, 0, 1, 0, 0, 3, 0, 1, 2, 1]
else
[0, 0, 1, 0, 0, 3, 0, 1, 2, 2])
else
(if i.val < 4783 then
[0, 0, 1, 0, 0, 3, 0, 2, 1, 1]
else
[0, 0, 1, 0, 0, 3, 0, 2, 2, 1]))))
else
(if i.val < 4792 then
(if i.val < 4788 then
(if i.val < 4786 then
(if i.val < 4785 then
[0, 0, 1, 0, 0, 3, 2, 1, 0, 3]
else
[0, 0, 1, 0, 0, 3, 2, 2, 1, 1])
else
(if i.val < 4787 then
[0, 0, 1, 0, 0, 3, 2, 2, 1, 3]
else
[0, 0, 1, 0, 0, 3, 2, 2, 3, 0]))
else
(if i.val < 4790 then
(if i.val < 4789 then
[0, 0, 1, 0, 0, 3, 3, 0, 0, 1]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2, 1])
else
(if i.val < 4791 then
[0, 0, 1, 0, 0, 3, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 3, 3, 2, 1, 1])))
else
(if i.val < 4796 then
(if i.val < 4794 then
(if i.val < 4793 then
[0, 0, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 0, 1, 0, 2, 1, 0, 0, 3, 3])
else
(if i.val < 4795 then
[0, 0, 1, 0, 2, 1, 0, 3, 3, 2]
else
[0, 0, 1, 0, 2, 1, 1, 0, 0, 3]))
else
(if i.val < 4798 then
(if i.val < 4797 then
[0, 0, 1, 0, 2, 1, 1, 0, 3, 0]
else
[0, 0, 1, 0, 2, 1, 1, 0, 3, 2])
else
(if i.val < 4799 then
[0, 0, 1, 0, 2, 1, 1, 0, 3, 3]
else
[0, 0, 1, 0, 2, 1, 1, 2, 3, 2]))))))
else
(if i.val < 4832 then
(if i.val < 4816 then
(if i.val < 4808 then
(if i.val < 4804 then
(if i.val < 4802 then
(if i.val < 4801 then
[0, 0, 1, 0, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 1, 3, 0, 0, 3])
else
(if i.val < 4803 then
[0, 0, 1, 0, 2, 1, 3, 0, 1, 2]
else
[0, 0, 1, 0, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 4806 then
(if i.val < 4805 then
[0, 0, 1, 0, 2, 1, 3, 3, 0, 0]
else
[0, 0, 1, 0, 2, 1, 3, 3, 0, 1])
else
(if i.val < 4807 then
[0, 0, 1, 0, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 0, 2, 2, 1, 0, 0, 3])))
else
(if i.val < 4812 then
(if i.val < 4810 then
(if i.val < 4809 then
[0, 0, 1, 0, 2, 2, 1, 0, 3, 0]
else
[0, 0, 1, 0, 2, 2, 1, 0, 3, 2])
else
(if i.val < 4811 then
[0, 0, 1, 0, 2, 2, 1, 0, 3, 3]
else
[0, 0, 1, 0, 2, 2, 1, 1, 3, 2]))
else
(if i.val < 4814 then
(if i.val < 4813 then
[0, 0, 1, 0, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 2, 1, 3, 0, 1])
else
(if i.val < 4815 then
[0, 0, 1, 0, 2, 2, 1, 3, 2, 1]
else
[0, 0, 1, 0, 2, 2, 1, 3, 3, 2]))))
else
(if i.val < 4824 then
(if i.val < 4820 then
(if i.val < 4818 then
(if i.val < 4817 then
[0, 0, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 0, 1, 0, 2, 2, 3, 0, 2, 1])
else
(if i.val < 4819 then
[0, 0, 1, 0, 2, 2, 3, 2, 2, 1]
else
[0, 0, 1, 0, 2, 2, 3, 2, 2, 3]))
else
(if i.val < 4822 then
(if i.val < 4821 then
[0, 0, 1, 0, 2, 2, 3, 3, 0, 0]
else
[0, 0, 1, 0, 2, 2, 3, 3, 2, 1])
else
(if i.val < 4823 then
[0, 0, 1, 0, 2, 2, 3, 3, 2, 2]
else
[0, 0, 1, 0, 2, 3, 0, 0, 2, 1])))
else
(if i.val < 4828 then
(if i.val < 4826 then
(if i.val < 4825 then
[0, 0, 1, 0, 2, 3, 0, 0, 2, 3]
else
[0, 0, 1, 0, 2, 3, 0, 0, 3, 2])
else
(if i.val < 4827 then
[0, 0, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 0, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 4830 then
(if i.val < 4829 then
[0, 0, 1, 0, 2, 3, 0, 2, 1, 3]
else
[0, 0, 1, 0, 2, 3, 2, 1, 0, 0])
else
(if i.val < 4831 then
[0, 0, 1, 0, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 0, 2, 3, 2, 2, 3, 0])))))
else
(if i.val < 4848 then
(if i.val < 4840 then
(if i.val < 4836 then
(if i.val < 4834 then
(if i.val < 4833 then
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 4835 then
[0, 0, 1, 0, 2, 3, 3, 0, 2, 2]
else
[0, 0, 1, 0, 3, 0, 0, 1, 1, 3]))
else
(if i.val < 4838 then
(if i.val < 4837 then
[0, 0, 1, 0, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 0, 3, 0, 0, 1, 3, 2])
else
(if i.val < 4839 then
[0, 0, 1, 0, 3, 0, 0, 2, 1, 1]
else
[0, 0, 1, 0, 3, 0, 0, 2, 2, 1])))
else
(if i.val < 4844 then
(if i.val < 4842 then
(if i.val < 4841 then
[0, 0, 1, 0, 3, 0, 0, 3, 2, 1]
else
[0, 0, 1, 0, 3, 0, 0, 3, 2, 2])
else
(if i.val < 4843 then
[0, 0, 1, 0, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 0, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 4846 then
(if i.val < 4845 then
[0, 0, 1, 0, 3, 0, 1, 2, 1, 1]
else
[0, 0, 1, 0, 3, 0, 1, 2, 2, 1])
else
(if i.val < 4847 then
[0, 0, 1, 0, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 0, 3, 0, 1, 2, 3, 0]))))
else
(if i.val < 4856 then
(if i.val < 4852 then
(if i.val < 4850 then
(if i.val < 4849 then
[0, 0, 1, 0, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 0, 3, 0, 2, 1, 0, 3])
else
(if i.val < 4851 then
[0, 0, 1, 0, 3, 0, 2, 1, 1, 3]
else
[0, 0, 1, 0, 3, 0, 2, 1, 3, 3]))
else
(if i.val < 4854 then
(if i.val < 4853 then
[0, 0, 1, 0, 3, 0, 2, 2, 1, 3]
else
[0, 0, 1, 0, 3, 0, 2, 2, 3, 0])
else
(if i.val < 4855 then
[0, 0, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 0, 3, 2, 1, 1, 0, 0])))
else
(if i.val < 4860 then
(if i.val < 4858 then
(if i.val < 4857 then
[0, 0, 1, 0, 3, 2, 2, 1, 0, 0]
else
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3])
else
(if i.val < 4859 then
[0, 0, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 0, 1, 0, 3, 2, 2, 1, 3, 2]))
else
(if i.val < 4862 then
(if i.val < 4861 then
[0, 0, 1, 0, 3, 2, 2, 3, 0, 0]
else
[0, 0, 1, 0, 3, 2, 2, 3, 0, 1])
else
(if i.val < 4863 then
[0, 0, 1, 0, 3, 3, 0, 0, 2, 3]
else
[0, 0, 1, 0, 3, 3, 0, 1, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0038 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 4928 then
(if i.val < 4896 then
(if i.val < 4880 then
(if i.val < 4872 then
(if i.val < 4868 then
(if i.val < 4866 then
(if i.val < 4865 then
[0, 0, 1, 0, 3, 3, 0, 1, 2, 3]
else
[0, 0, 1, 0, 3, 3, 0, 2, 1, 3])
else
(if i.val < 4867 then
[0, 0, 1, 0, 3, 3, 0, 2, 2, 1]
else
[0, 0, 1, 0, 3, 3, 0, 2, 2, 3]))
else
(if i.val < 4870 then
(if i.val < 4869 then
[0, 0, 1, 0, 3, 3, 0, 2, 3, 3]
else
[0, 0, 1, 0, 3, 3, 2, 1, 0, 3])
else
(if i.val < 4871 then
[0, 0, 1, 1, 0, 0, 2, 1, 0, 3]
else
[0, 0, 1, 1, 0, 0, 2, 1, 1, 3])))
else
(if i.val < 4876 then
(if i.val < 4874 then
(if i.val < 4873 then
[0, 0, 1, 1, 0, 0, 2, 1, 3, 0]
else
[0, 0, 1, 1, 0, 0, 2, 1, 3, 3])
else
(if i.val < 4875 then
[0, 0, 1, 1, 0, 0, 2, 2, 1, 3]
else
[0, 0, 1, 1, 0, 0, 2, 2, 3, 0]))
else
(if i.val < 4878 then
(if i.val < 4877 then
[0, 0, 1, 1, 0, 0, 2, 2, 3, 2]
else
[0, 0, 1, 1, 0, 0, 2, 2, 3, 3])
else
(if i.val < 4879 then
[0, 0, 1, 1, 0, 0, 2, 3, 0, 1]
else
[0, 0, 1, 1, 0, 0, 2, 3, 2, 1]))))
else
(if i.val < 4888 then
(if i.val < 4884 then
(if i.val < 4882 then
(if i.val < 4881 then
[0, 0, 1, 1, 0, 0, 2, 3, 3, 2]
else
[0, 0, 1, 1, 0, 0, 3, 0, 0, 3])
else
(if i.val < 4883 then
[0, 0, 1, 1, 0, 0, 3, 0, 1, 2]
else
[0, 0, 1, 1, 0, 0, 3, 0, 2, 1]))
else
(if i.val < 4886 then
(if i.val < 4885 then
[0, 0, 1, 1, 0, 0, 3, 2, 1, 1]
else
[0, 0, 1, 1, 0, 0, 3, 2, 2, 3])
else
(if i.val < 4887 then
[0, 0, 1, 1, 0, 0, 3, 3, 2, 2]
else
[0, 0, 1, 1, 0, 2, 1, 0, 0, 3])))
else
(if i.val < 4892 then
(if i.val < 4890 then
(if i.val < 4889 then
[0, 0, 1, 1, 0, 2, 1, 0, 3, 0]
else
[0, 0, 1, 1, 0, 2, 1, 0, 3, 2])
else
(if i.val < 4891 then
[0, 0, 1, 1, 0, 2, 1, 0, 3, 3]
else
[0, 0, 1, 1, 0, 2, 1, 1, 0, 0]))
else
(if i.val < 4894 then
(if i.val < 4893 then
[0, 0, 1, 1, 0, 2, 1, 1, 2, 3]
else
[0, 0, 1, 1, 0, 2, 1, 3, 0, 1])
else
(if i.val < 4895 then
[0, 0, 1, 1, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 1, 0, 2, 2, 1, 0, 3])))))
else
(if i.val < 4912 then
(if i.val < 4904 then
(if i.val < 4900 then
(if i.val < 4898 then
(if i.val < 4897 then
[0, 0, 1, 1, 0, 2, 2, 1, 1, 3]
else
[0, 0, 1, 1, 0, 2, 2, 1, 3, 0])
else
(if i.val < 4899 then
[0, 0, 1, 1, 0, 2, 2, 1, 3, 2]
else
[0, 0, 1, 1, 0, 2, 2, 1, 3, 3]))
else
(if i.val < 4902 then
(if i.val < 4901 then
[0, 0, 1, 1, 0, 2, 2, 3, 0, 0]
else
[0, 0, 1, 1, 0, 2, 2, 3, 0, 1])
else
(if i.val < 4903 then
[0, 0, 1, 1, 0, 2, 2, 3, 2, 1]
else
[0, 0, 1, 1, 0, 2, 2, 3, 3, 2])))
else
(if i.val < 4908 then
(if i.val < 4906 then
(if i.val < 4905 then
[0, 0, 1, 1, 0, 2, 3, 0, 1, 2]
else
[0, 0, 1, 1, 0, 2, 3, 0, 2, 1])
else
(if i.val < 4907 then
[0, 0, 1, 1, 0, 2, 3, 0, 2, 2]
else
[0, 0, 1, 1, 0, 2, 3, 2, 2, 3]))
else
(if i.val < 4910 then
(if i.val < 4909 then
[0, 0, 1, 1, 0, 2, 3, 3, 0, 1]
else
[0, 0, 1, 1, 0, 3, 0, 0, 2, 2])
else
(if i.val < 4911 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 3, 0, 2, 1, 1]))))
else
(if i.val < 4920 then
(if i.val < 4916 then
(if i.val < 4914 then
(if i.val < 4913 then
[0, 0, 1, 1, 0, 3, 0, 2, 1, 3]
else
[0, 0, 1, 1, 0, 3, 0, 2, 2, 1])
else
(if i.val < 4915 then
[0, 0, 1, 1, 0, 3, 0, 2, 2, 3]
else
[0, 0, 1, 1, 0, 3, 2, 1, 0, 3]))
else
(if i.val < 4918 then
(if i.val < 4917 then
[0, 0, 1, 1, 0, 3, 2, 2, 3, 0]
else
[0, 0, 1, 1, 0, 3, 3, 0, 1, 2])
else
(if i.val < 4919 then
[0, 0, 1, 1, 0, 3, 3, 0, 2, 1]
else
[0, 0, 1, 1, 0, 3, 3, 0, 2, 2])))
else
(if i.val < 4924 then
(if i.val < 4922 then
(if i.val < 4921 then
[0, 0, 1, 1, 0, 3, 3, 2, 1, 1]
else
[0, 0, 1, 1, 0, 3, 3, 2, 2, 1])
else
(if i.val < 4923 then
[0, 0, 1, 1, 2, 1, 0, 0, 1, 3]
else
[0, 0, 1, 1, 2, 1, 0, 0, 3, 3]))
else
(if i.val < 4926 then
(if i.val < 4925 then
[0, 0, 1, 1, 2, 1, 0, 3, 0, 1]
else
[0, 0, 1, 1, 2, 1, 0, 3, 2, 1])
else
(if i.val < 4927 then
[0, 0, 1, 1, 2, 1, 0, 3, 3, 2]
else
[0, 0, 1, 1, 2, 1, 1, 0, 3, 3]))))))
else
(if i.val < 4960 then
(if i.val < 4944 then
(if i.val < 4936 then
(if i.val < 4932 then
(if i.val < 4930 then
(if i.val < 4929 then
[0, 0, 1, 1, 2, 1, 1, 2, 3, 2]
else
[0, 0, 1, 1, 2, 1, 1, 2, 3, 3])
else
(if i.val < 4931 then
[0, 0, 1, 1, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 1, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 4934 then
(if i.val < 4933 then
[0, 0, 1, 1, 2, 1, 1, 3, 2, 2]
else
[0, 0, 1, 1, 2, 1, 1, 3, 3, 2])
else
(if i.val < 4935 then
[0, 0, 1, 1, 2, 1, 3, 0, 0, 3]
else
[0, 0, 1, 1, 2, 1, 3, 0, 1, 2])))
else
(if i.val < 4940 then
(if i.val < 4938 then
(if i.val < 4937 then
[0, 0, 1, 1, 2, 1, 3, 0, 2, 2]
else
[0, 0, 1, 1, 2, 1, 3, 2, 1, 1])
else
(if i.val < 4939 then
[0, 0, 1, 1, 2, 1, 3, 2, 2, 1]
else
[0, 0, 1, 1, 2, 1, 3, 2, 2, 3]))
else
(if i.val < 4942 then
(if i.val < 4941 then
[0, 0, 1, 1, 2, 1, 3, 3, 0, 0]
else
[0, 0, 1, 1, 2, 1, 3, 3, 2, 1])
else
(if i.val < 4943 then
[0, 0, 1, 1, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 1, 2, 2, 1, 0, 3, 0]))))
else
(if i.val < 4952 then
(if i.val < 4948 then
(if i.val < 4946 then
(if i.val < 4945 then
[0, 0, 1, 1, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 1, 2, 2, 1, 0, 3, 3])
else
(if i.val < 4947 then
[0, 0, 1, 1, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 1, 2, 2, 1, 1, 3, 3]))
else
(if i.val < 4950 then
(if i.val < 4949 then
[0, 0, 1, 1, 2, 2, 1, 3, 0, 0]
else
[0, 0, 1, 1, 2, 2, 1, 3, 0, 1])
else
(if i.val < 4951 then
[0, 0, 1, 1, 2, 2, 1, 3, 3, 2]
else
[0, 0, 1, 1, 2, 2, 3, 0, 0, 3])))
else
(if i.val < 4956 then
(if i.val < 4954 then
(if i.val < 4953 then
[0, 0, 1, 1, 2, 2, 3, 0, 1, 2]
else
[0, 0, 1, 1, 2, 2, 3, 2, 1, 1])
else
(if i.val < 4955 then
[0, 0, 1, 1, 2, 2, 3, 2, 2, 1]
else
[0, 0, 1, 1, 2, 2, 3, 2, 2, 3]))
else
(if i.val < 4958 then
(if i.val < 4957 then
[0, 0, 1, 1, 2, 2, 3, 3, 2, 2]
else
[0, 0, 1, 1, 2, 3, 0, 0, 1, 1])
else
(if i.val < 4959 then
[0, 0, 1, 1, 2, 3, 0, 0, 2, 1]
else
[0, 0, 1, 1, 2, 3, 0, 0, 2, 2])))))
else
(if i.val < 4976 then
(if i.val < 4968 then
(if i.val < 4964 then
(if i.val < 4962 then
(if i.val < 4961 then
[0, 0, 1, 1, 2, 3, 0, 0, 2, 3]
else
[0, 0, 1, 1, 2, 3, 0, 0, 3, 2])
else
(if i.val < 4963 then
[0, 0, 1, 1, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 2, 3, 0, 1, 2, 2]))
else
(if i.val < 4966 then
(if i.val < 4965 then
[0, 0, 1, 1, 2, 3, 0, 2, 1, 1]
else
[0, 0, 1, 1, 2, 3, 0, 2, 1, 3])
else
(if i.val < 4967 then
[0, 0, 1, 1, 2, 3, 0, 2, 2, 1]
else
[0, 0, 1, 1, 2, 3, 2, 1, 0, 0])))
else
(if i.val < 4972 then
(if i.val < 4970 then
(if i.val < 4969 then
[0, 0, 1, 1, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 1, 2, 3, 3, 0, 0, 1])
else
(if i.val < 4971 then
[0, 0, 1, 1, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 1, 2, 3, 3, 0, 2, 2]))
else
(if i.val < 4974 then
(if i.val < 4973 then
[0, 0, 1, 1, 2, 3, 3, 0, 2, 3]
else
[0, 0, 1, 1, 3, 0, 0, 1, 1, 3])
else
(if i.val < 4975 then
[0, 0, 1, 1, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 1, 3, 0, 0, 2, 1, 1]))))
else
(if i.val < 4984 then
(if i.val < 4980 then
(if i.val < 4978 then
(if i.val < 4977 then
[0, 0, 1, 1, 3, 0, 0, 2, 2, 1]
else
[0, 0, 1, 1, 3, 0, 0, 3, 2, 1])
else
(if i.val < 4979 then
[0, 0, 1, 1, 3, 0, 0, 3, 2, 2]
else
[0, 0, 1, 1, 3, 0, 1, 1, 2, 1]))
else
(if i.val < 4982 then
(if i.val < 4981 then
[0, 0, 1, 1, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 1, 3, 0, 1, 2, 3, 0])
else
(if i.val < 4983 then
[0, 0, 1, 1, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 1, 3, 0, 2, 1, 0, 3])))
else
(if i.val < 4988 then
(if i.val < 4986 then
(if i.val < 4985 then
[0, 0, 1, 1, 3, 0, 2, 1, 1, 3]
else
[0, 0, 1, 1, 3, 0, 2, 1, 3, 2])
else
(if i.val < 4987 then
[0, 0, 1, 1, 3, 0, 2, 2, 3, 0]
else
[0, 0, 1, 1, 3, 0, 2, 2, 3, 3]))
else
(if i.val < 4990 then
(if i.val < 4989 then
[0, 0, 1, 1, 3, 2, 1, 0, 0, 3]
else
[0, 0, 1, 1, 3, 2, 1, 1, 0, 0])
else
(if i.val < 4991 then
[0, 0, 1, 1, 3, 2, 2, 1, 1, 3]
else
[0, 0, 1, 1, 3, 3, 0, 0, 2, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0039 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5056 then
(if i.val < 5024 then
(if i.val < 5008 then
(if i.val < 5000 then
(if i.val < 4996 then
(if i.val < 4994 then
(if i.val < 4993 then
[0, 0, 1, 1, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 3, 3, 0, 1, 2, 2])
else
(if i.val < 4995 then
[0, 0, 1, 1, 3, 3, 0, 1, 2, 3]
else
[0, 0, 1, 1, 3, 3, 2, 1, 0, 0]))
else
(if i.val < 4998 then
(if i.val < 4997 then
[0, 0, 1, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 1, 0, 0, 1, 2, 3])
else
(if i.val < 4999 then
[0, 0, 1, 2, 1, 0, 0, 1, 3, 3]
else
[0, 0, 1, 2, 1, 0, 0, 3, 0, 0])))
else
(if i.val < 5004 then
(if i.val < 5002 then
(if i.val < 5001 then
[0, 0, 1, 2, 1, 0, 0, 3, 0, 1]
else
[0, 0, 1, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 5003 then
[0, 0, 1, 2, 1, 0, 3, 0, 0, 3]
else
[0, 0, 1, 2, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 5006 then
(if i.val < 5005 then
[0, 0, 1, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 5007 then
[0, 0, 1, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 2, 1, 0, 3, 2, 2, 3]))))
else
(if i.val < 5016 then
(if i.val < 5012 then
(if i.val < 5010 then
(if i.val < 5009 then
[0, 0, 1, 2, 1, 1, 0, 0, 3, 0]
else
[0, 0, 1, 2, 1, 1, 0, 0, 3, 2])
else
(if i.val < 5011 then
[0, 0, 1, 2, 1, 1, 0, 0, 3, 3]
else
[0, 0, 1, 2, 1, 1, 0, 2, 1, 3]))
else
(if i.val < 5014 then
(if i.val < 5013 then
[0, 0, 1, 2, 1, 1, 0, 2, 3, 2]
else
[0, 0, 1, 2, 1, 1, 0, 3, 0, 1])
else
(if i.val < 5015 then
[0, 0, 1, 2, 1, 1, 0, 3, 2, 1]
else
[0, 0, 1, 2, 1, 1, 2, 3, 0, 0])))
else
(if i.val < 5020 then
(if i.val < 5018 then
(if i.val < 5017 then
[0, 0, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 1, 2, 1, 1, 2, 3, 2, 1])
else
(if i.val < 5019 then
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2]
else
[0, 0, 1, 2, 1, 1, 3, 0, 2, 2]))
else
(if i.val < 5022 then
(if i.val < 5021 then
[0, 0, 1, 2, 1, 1, 3, 2, 1, 1]
else
[0, 0, 1, 2, 1, 1, 3, 2, 2, 1])
else
(if i.val < 5023 then
[0, 0, 1, 2, 1, 1, 3, 2, 2, 3]
else
[0, 0, 1, 2, 1, 1, 3, 3, 2, 2])))))
else
(if i.val < 5040 then
(if i.val < 5032 then
(if i.val < 5028 then
(if i.val < 5026 then
(if i.val < 5025 then
[0, 0, 1, 2, 1, 3, 0, 0, 2, 2]
else
[0, 0, 1, 2, 1, 3, 0, 0, 2, 3])
else
(if i.val < 5027 then
[0, 0, 1, 2, 1, 3, 0, 0, 3, 2]
else
[0, 0, 1, 2, 1, 3, 0, 1, 2, 1]))
else
(if i.val < 5030 then
(if i.val < 5029 then
[0, 0, 1, 2, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 1, 3, 0, 1, 2, 3])
else
(if i.val < 5031 then
[0, 0, 1, 2, 1, 3, 0, 2, 2, 3]
else
[0, 0, 1, 2, 1, 3, 2, 1, 0, 0])))
else
(if i.val < 5036 then
(if i.val < 5034 then
(if i.val < 5033 then
[0, 0, 1, 2, 1, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 1, 3, 2, 2, 1, 1])
else
(if i.val < 5035 then
[0, 0, 1, 2, 1, 3, 3, 0, 0, 1]
else
[0, 0, 1, 2, 1, 3, 3, 0, 1, 2]))
else
(if i.val < 5038 then
(if i.val < 5037 then
[0, 0, 1, 2, 1, 3, 3, 0, 2, 3]
else
[0, 0, 1, 2, 2, 1, 0, 0, 3, 0])
else
(if i.val < 5039 then
[0, 0, 1, 2, 2, 1, 0, 0, 3, 3]
else
[0, 0, 1, 2, 2, 1, 0, 3, 2, 1]))))
else
(if i.val < 5048 then
(if i.val < 5044 then
(if i.val < 5042 then
(if i.val < 5041 then
[0, 0, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 5043 then
[0, 0, 1, 2, 2, 1, 3, 0, 0, 1]
else
[0, 0, 1, 2, 2, 1, 3, 0, 2, 3]))
else
(if i.val < 5046 then
(if i.val < 5045 then
[0, 0, 1, 2, 2, 1, 3, 2, 1, 1]
else
[0, 0, 1, 2, 2, 1, 3, 2, 2, 3])
else
(if i.val < 5047 then
[0, 0, 1, 2, 2, 1, 3, 3, 0, 0]
else
[0, 0, 1, 2, 2, 3, 0, 0, 2, 3])))
else
(if i.val < 5052 then
(if i.val < 5050 then
(if i.val < 5049 then
[0, 0, 1, 2, 2, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 5051 then
[0, 0, 1, 2, 2, 3, 0, 2, 2, 3]
else
[0, 0, 1, 2, 2, 3, 2, 1, 0, 0]))
else
(if i.val < 5054 then
(if i.val < 5053 then
[0, 0, 1, 2, 2, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 2, 3, 2, 2, 1, 1])
else
(if i.val < 5055 then
[0, 0, 1, 2, 2, 3, 2, 2, 1, 3]
else
[0, 0, 1, 2, 2, 3, 3, 0, 2, 3]))))))
else
(if i.val < 5088 then
(if i.val < 5072 then
(if i.val < 5064 then
(if i.val < 5060 then
(if i.val < 5058 then
(if i.val < 5057 then
[0, 0, 1, 2, 3, 0, 0, 1, 1, 3]
else
[0, 0, 1, 2, 3, 0, 0, 1, 2, 1])
else
(if i.val < 5059 then
[0, 0, 1, 2, 3, 0, 0, 1, 2, 3]
else
[0, 0, 1, 2, 3, 0, 0, 1, 3, 2]))
else
(if i.val < 5062 then
(if i.val < 5061 then
[0, 0, 1, 2, 3, 0, 0, 2, 2, 1]
else
[0, 0, 1, 2, 3, 0, 0, 2, 2, 3])
else
(if i.val < 5063 then
[0, 0, 1, 2, 3, 0, 0, 2, 3, 3]
else
[0, 0, 1, 2, 3, 0, 0, 3, 2, 2])))
else
(if i.val < 5068 then
(if i.val < 5066 then
(if i.val < 5065 then
[0, 0, 1, 2, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 1, 2, 2])
else
(if i.val < 5067 then
[0, 0, 1, 2, 3, 0, 1, 2, 1, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 2, 1]))
else
(if i.val < 5070 then
(if i.val < 5069 then
[0, 0, 1, 2, 3, 0, 1, 2, 3, 3]
else
[0, 0, 1, 2, 3, 0, 2, 1, 1, 3])
else
(if i.val < 5071 then
[0, 0, 1, 2, 3, 0, 2, 2, 1, 3]
else
[0, 0, 1, 2, 3, 0, 2, 2, 3, 0]))))
else
(if i.val < 5080 then
(if i.val < 5076 then
(if i.val < 5074 then
(if i.val < 5073 then
[0, 0, 1, 2, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 2, 3, 0, 2, 3, 3, 0])
else
(if i.val < 5075 then
[0, 0, 1, 2, 3, 2, 1, 0, 0, 3]
else
[0, 0, 1, 2, 3, 2, 1, 0, 3, 3]))
else
(if i.val < 5078 then
(if i.val < 5077 then
[0, 0, 1, 2, 3, 2, 1, 1, 2, 3]
else
[0, 0, 1, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 5079 then
[0, 0, 1, 2, 3, 2, 2, 3, 0, 0]
else
[0, 0, 1, 2, 3, 3, 0, 0, 1, 1])))
else
(if i.val < 5084 then
(if i.val < 5082 then
(if i.val < 5081 then
[0, 0, 1, 2, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 5083 then
[0, 0, 1, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 3, 0, 1, 2, 2]))
else
(if i.val < 5086 then
(if i.val < 5085 then
[0, 0, 1, 2, 3, 3, 0, 2, 1, 3]
else
[0, 0, 1, 2, 3, 3, 0, 2, 2, 1])
else
(if i.val < 5087 then
[0, 0, 1, 2, 3, 3, 0, 2, 2, 3]
else
[0, 0, 1, 2, 3, 3, 0, 2, 3, 3])))))
else
(if i.val < 5104 then
(if i.val < 5096 then
(if i.val < 5092 then
(if i.val < 5090 then
(if i.val < 5089 then
[0, 0, 1, 2, 3, 3, 2, 1, 0, 0]
else
[0, 0, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 5091 then
[0, 0, 1, 3, 0, 0, 1, 1, 2, 1]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1, 3]))
else
(if i.val < 5094 then
(if i.val < 5093 then
[0, 0, 1, 3, 0, 0, 1, 2, 3, 0]
else
[0, 0, 1, 3, 0, 0, 1, 2, 3, 2])
else
(if i.val < 5095 then
[0, 0, 1, 3, 0, 0, 1, 2, 3, 3]
else
[0, 0, 1, 3, 0, 0, 1, 3, 2, 1])))
else
(if i.val < 5100 then
(if i.val < 5098 then
(if i.val < 5097 then
[0, 0, 1, 3, 0, 0, 2, 2, 3, 2]
else
[0, 0, 1, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 5099 then
[0, 0, 1, 3, 0, 0, 3, 2, 1, 1]
else
[0, 0, 1, 3, 0, 0, 3, 2, 2, 1]))
else
(if i.val < 5102 then
(if i.val < 5101 then
[0, 0, 1, 3, 0, 0, 3, 2, 2, 3]
else
[0, 0, 1, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 5103 then
[0, 0, 1, 3, 0, 1, 1, 0, 2, 2]
else
[0, 0, 1, 3, 0, 1, 1, 0, 3, 2]))))
else
(if i.val < 5112 then
(if i.val < 5108 then
(if i.val < 5106 then
(if i.val < 5105 then
[0, 0, 1, 3, 0, 1, 1, 0, 3, 3]
else
[0, 0, 1, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5107 then
[0, 0, 1, 3, 0, 1, 2, 2, 1, 3]
else
[0, 0, 1, 3, 0, 1, 2, 2, 3, 0]))
else
(if i.val < 5110 then
(if i.val < 5109 then
[0, 0, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 1, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 5111 then
[0, 0, 1, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 3, 0, 2, 1, 0, 3, 2])))
else
(if i.val < 5116 then
(if i.val < 5114 then
(if i.val < 5113 then
[0, 0, 1, 3, 0, 2, 1, 1, 0, 0]
else
[0, 0, 1, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 5115 then
[0, 0, 1, 3, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 3, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 5118 then
(if i.val < 5117 then
[0, 0, 1, 3, 0, 2, 2, 1, 1, 3]
else
[0, 0, 1, 3, 0, 2, 2, 3, 0, 1])
else
(if i.val < 5119 then
[0, 0, 1, 3, 0, 2, 3, 3, 0, 1]
else
[0, 0, 1, 3, 2, 1, 0, 0, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0040 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5184 then
(if i.val < 5152 then
(if i.val < 5136 then
(if i.val < 5128 then
(if i.val < 5124 then
(if i.val < 5122 then
(if i.val < 5121 then
[0, 0, 1, 3, 2, 1, 0, 3, 3, 0]
else
[0, 0, 1, 3, 2, 1, 1, 0, 0, 3])
else
(if i.val < 5123 then
[0, 0, 1, 3, 2, 2, 1, 0, 3, 0]
else
[0, 0, 1, 3, 2, 2, 1, 0, 3, 3]))
else
(if i.val < 5126 then
(if i.val < 5125 then
[0, 0, 1, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 5127 then
[0, 0, 1, 3, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 3, 3, 0, 0, 1, 2, 3])))
else
(if i.val < 5132 then
(if i.val < 5130 then
(if i.val < 5129 then
[0, 0, 1, 3, 3, 0, 1, 1, 2, 2]
else
[0, 0, 1, 3, 3, 0, 1, 2, 2, 3])
else
(if i.val < 5131 then
[0, 0, 1, 3, 3, 0, 1, 2, 3, 0]
else
[0, 0, 1, 3, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 5134 then
(if i.val < 5133 then
[0, 0, 1, 3, 3, 0, 2, 1, 1, 3]
else
[0, 0, 1, 3, 3, 0, 2, 1, 3, 2])
else
(if i.val < 5135 then
[0, 0, 1, 3, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 3, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 5144 then
(if i.val < 5140 then
(if i.val < 5138 then
(if i.val < 5137 then
[0, 0, 1, 3, 3, 2, 1, 0, 3, 3]
else
[0, 0, 1, 3, 3, 2, 1, 1, 2, 3])
else
(if i.val < 5139 then
[0, 0, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 0, 2, 1, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 5142 then
(if i.val < 5141 then
[0, 0, 2, 1, 0, 0, 1, 2, 3, 2]
else
[0, 0, 2, 1, 0, 0, 1, 3, 0, 0])
else
(if i.val < 5143 then
[0, 0, 2, 1, 0, 0, 1, 3, 2, 1]
else
[0, 0, 2, 1, 0, 0, 1, 3, 3, 2])))
else
(if i.val < 5148 then
(if i.val < 5146 then
(if i.val < 5145 then
[0, 0, 2, 1, 0, 0, 3, 0, 0, 3]
else
[0, 0, 2, 1, 0, 0, 3, 2, 2, 1])
else
(if i.val < 5147 then
[0, 0, 2, 1, 0, 0, 3, 2, 2, 3]
else
[0, 0, 2, 1, 0, 0, 3, 3, 2, 2]))
else
(if i.val < 5150 then
(if i.val < 5149 then
[0, 0, 2, 1, 0, 3, 0, 0, 1, 1]
else
[0, 0, 2, 1, 0, 3, 0, 0, 2, 1])
else
(if i.val < 5151 then
[0, 0, 2, 1, 0, 3, 0, 1, 2, 1]
else
[0, 0, 2, 1, 0, 3, 0, 1, 2, 2])))))
else
(if i.val < 5168 then
(if i.val < 5160 then
(if i.val < 5156 then
(if i.val < 5154 then
(if i.val < 5153 then
[0, 0, 2, 1, 0, 3, 0, 1, 2, 3]
else
[0, 0, 2, 1, 0, 3, 0, 2, 2, 1])
else
(if i.val < 5155 then
[0, 0, 2, 1, 0, 3, 2, 1, 0, 0]
else
[0, 0, 2, 1, 0, 3, 2, 1, 0, 3]))
else
(if i.val < 5158 then
(if i.val < 5157 then
[0, 0, 2, 1, 0, 3, 2, 2, 1, 3]
else
[0, 0, 2, 1, 0, 3, 2, 2, 3, 0])
else
(if i.val < 5159 then
[0, 0, 2, 1, 0, 3, 3, 0, 2, 2]
else
[0, 0, 2, 1, 0, 3, 3, 0, 2, 3])))
else
(if i.val < 5164 then
(if i.val < 5162 then
(if i.val < 5161 then
[0, 0, 2, 1, 0, 3, 3, 2, 1, 1]
else
[0, 0, 2, 1, 1, 0, 0, 2, 1, 3])
else
(if i.val < 5163 then
[0, 0, 2, 1, 1, 0, 0, 3, 0, 0]
else
[0, 0, 2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 5166 then
(if i.val < 5165 then
[0, 0, 2, 1, 1, 0, 0, 3, 2, 1]
else
[0, 0, 2, 1, 1, 0, 0, 3, 2, 2])
else
(if i.val < 5167 then
[0, 0, 2, 1, 1, 0, 0, 3, 3, 2]
else
[0, 0, 2, 1, 1, 0, 2, 1, 1, 3]))))
else
(if i.val < 5176 then
(if i.val < 5172 then
(if i.val < 5170 then
(if i.val < 5169 then
[0, 0, 2, 1, 1, 0, 2, 1, 3, 2]
else
[0, 0, 2, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 5171 then
[0, 0, 2, 1, 1, 0, 2, 3, 2, 1]
else
[0, 0, 2, 1, 1, 0, 2, 3, 3, 2]))
else
(if i.val < 5174 then
(if i.val < 5173 then
[0, 0, 2, 1, 1, 0, 3, 0, 0, 3]
else
[0, 0, 2, 1, 1, 0, 3, 0, 1, 2])
else
(if i.val < 5175 then
[0, 0, 2, 1, 1, 0, 3, 0, 2, 1]
else
[0, 0, 2, 1, 1, 0, 3, 0, 2, 2])))
else
(if i.val < 5180 then
(if i.val < 5178 then
(if i.val < 5177 then
[0, 0, 2, 1, 1, 0, 3, 2, 1, 1]
else
[0, 0, 2, 1, 1, 0, 3, 2, 2, 3])
else
(if i.val < 5179 then
[0, 0, 2, 1, 1, 2, 3, 0, 1, 2]
else
[0, 0, 2, 1, 1, 2, 3, 2, 1, 1]))
else
(if i.val < 5182 then
(if i.val < 5181 then
[0, 0, 2, 1, 1, 2, 3, 2, 2, 3]
else
[0, 0, 2, 1, 1, 3, 0, 0, 1, 1])
else
(if i.val < 5183 then
[0, 0, 2, 1, 1, 3, 0, 1, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 1, 2, 2]))))))
else
(if i.val < 5216 then
(if i.val < 5200 then
(if i.val < 5192 then
(if i.val < 5188 then
(if i.val < 5186 then
(if i.val < 5185 then
[0, 0, 2, 1, 1, 3, 0, 1, 2, 3]
else
[0, 0, 2, 1, 1, 3, 0, 2, 1, 1])
else
(if i.val < 5187 then
[0, 0, 2, 1, 1, 3, 3, 0, 1, 2]
else
[0, 0, 2, 1, 3, 0, 0, 1, 1, 3]))
else
(if i.val < 5190 then
(if i.val < 5189 then
[0, 0, 2, 1, 3, 0, 0, 1, 2, 1]
else
[0, 0, 2, 1, 3, 0, 0, 1, 2, 3])
else
(if i.val < 5191 then
[0, 0, 2, 1, 3, 0, 0, 2, 2, 1]
else
[0, 0, 2, 1, 3, 0, 0, 2, 2, 3])))
else
(if i.val < 5196 then
(if i.val < 5194 then
(if i.val < 5193 then
[0, 0, 2, 1, 3, 0, 0, 3, 2, 1]
else
[0, 0, 2, 1, 3, 0, 0, 3, 2, 2])
else
(if i.val < 5195 then
[0, 0, 2, 1, 3, 0, 2, 2, 3, 3]
else
[0, 0, 2, 1, 3, 2, 1, 1, 0, 0]))
else
(if i.val < 5198 then
(if i.val < 5197 then
[0, 0, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 0, 2, 1, 3, 2, 2, 1, 3, 2])
else
(if i.val < 5199 then
[0, 0, 2, 1, 3, 2, 2, 3, 0, 0]
else
[0, 0, 2, 1, 3, 2, 2, 3, 0, 1]))))
else
(if i.val < 5208 then
(if i.val < 5204 then
(if i.val < 5202 then
(if i.val < 5201 then
[0, 0, 2, 1, 3, 3, 0, 0, 2, 1]
else
[0, 0, 2, 1, 3, 3, 0, 1, 2, 3])
else
(if i.val < 5203 then
[0, 0, 2, 1, 3, 3, 0, 2, 1, 3]
else
[0, 0, 2, 1, 3, 3, 0, 2, 2, 3]))
else
(if i.val < 5206 then
(if i.val < 5205 then
[0, 0, 2, 1, 3, 3, 0, 2, 3, 3]
else
[0, 0, 2, 1, 3, 3, 2, 1, 0, 0])
else
(if i.val < 5207 then
[0, 0, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 2, 1, 3, 3, 2, 2, 1, 1])))
else
(if i.val < 5212 then
(if i.val < 5210 then
(if i.val < 5209 then
[0, 0, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 2, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 5211 then
[0, 0, 2, 2, 1, 0, 3, 0, 0, 1]
else
[0, 0, 2, 2, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 5214 then
(if i.val < 5213 then
[0, 0, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 0, 2, 2])
else
(if i.val < 5215 then
[0, 0, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 2, 2, 1, 0, 3, 2, 2, 3])))))
else
(if i.val < 5232 then
(if i.val < 5224 then
(if i.val < 5220 then
(if i.val < 5218 then
(if i.val < 5217 then
[0, 0, 2, 2, 1, 1, 0, 0, 3, 0]
else
[0, 0, 2, 2, 1, 1, 0, 3, 0, 1])
else
(if i.val < 5219 then
[0, 0, 2, 2, 1, 1, 0, 3, 2, 1]
else
[0, 0, 2, 2, 1, 1, 0, 3, 3, 2]))
else
(if i.val < 5222 then
(if i.val < 5221 then
[0, 0, 2, 2, 1, 1, 3, 0, 1, 2]
else
[0, 0, 2, 2, 1, 1, 3, 2, 1, 1])
else
(if i.val < 5223 then
[0, 0, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 0, 2, 2, 1, 3, 0, 0, 2, 3])))
else
(if i.val < 5228 then
(if i.val < 5226 then
(if i.val < 5225 then
[0, 0, 2, 2, 1, 3, 0, 1, 2, 1]
else
[0, 0, 2, 2, 1, 3, 0, 1, 2, 2])
else
(if i.val < 5227 then
[0, 0, 2, 2, 1, 3, 0, 1, 2, 3]
else
[0, 0, 2, 2, 1, 3, 2, 1, 0, 3]))
else
(if i.val < 5230 then
(if i.val < 5229 then
[0, 0, 2, 2, 1, 3, 2, 2, 1, 1]
else
[0, 0, 2, 2, 1, 3, 2, 2, 1, 3])
else
(if i.val < 5231 then
[0, 0, 2, 2, 1, 3, 3, 0, 1, 2]
else
[0, 0, 2, 2, 1, 3, 3, 0, 2, 3]))))
else
(if i.val < 5240 then
(if i.val < 5236 then
(if i.val < 5234 then
(if i.val < 5233 then
[0, 0, 2, 2, 1, 3, 3, 2, 2, 1]
else
[0, 0, 2, 2, 3, 0, 0, 1, 1, 3])
else
(if i.val < 5235 then
[0, 0, 2, 2, 3, 0, 0, 1, 2, 1]
else
[0, 0, 2, 2, 3, 0, 0, 2, 1, 1]))
else
(if i.val < 5238 then
(if i.val < 5237 then
[0, 0, 2, 2, 3, 0, 0, 2, 2, 1]
else
[0, 0, 2, 2, 3, 0, 0, 2, 2, 3])
else
(if i.val < 5239 then
[0, 0, 2, 2, 3, 0, 0, 3, 2, 2]
else
[0, 0, 2, 2, 3, 0, 1, 1, 2, 2])))
else
(if i.val < 5244 then
(if i.val < 5242 then
(if i.val < 5241 then
[0, 0, 2, 2, 3, 0, 1, 2, 2, 1]
else
[0, 0, 2, 2, 3, 0, 2, 1, 0, 3])
else
(if i.val < 5243 then
[0, 0, 2, 2, 3, 0, 2, 1, 1, 3]
else
[0, 0, 2, 2, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 5246 then
(if i.val < 5245 then
[0, 0, 2, 2, 3, 2, 1, 0, 0, 3]
else
[0, 0, 2, 2, 3, 2, 1, 0, 3, 3])
else
(if i.val < 5247 then
[0, 0, 2, 2, 3, 2, 1, 1, 2, 3]
else
[0, 0, 2, 2, 3, 2, 2, 1, 0, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0041 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5312 then
(if i.val < 5280 then
(if i.val < 5264 then
(if i.val < 5256 then
(if i.val < 5252 then
(if i.val < 5250 then
(if i.val < 5249 then
[0, 0, 2, 2, 3, 2, 2, 1, 1, 3]
else
[0, 0, 2, 2, 3, 2, 2, 1, 3, 2])
else
(if i.val < 5251 then
[0, 0, 2, 2, 3, 3, 0, 0, 2, 3]
else
[0, 0, 2, 2, 3, 3, 0, 2, 1, 3]))
else
(if i.val < 5254 then
(if i.val < 5253 then
[0, 0, 2, 2, 3, 3, 0, 2, 2, 3]
else
[0, 0, 2, 2, 3, 3, 2, 1, 0, 0])
else
(if i.val < 5255 then
[0, 0, 2, 3, 0, 0, 1, 1, 2, 2]
else
[0, 0, 2, 3, 0, 0, 1, 2, 1, 3])))
else
(if i.val < 5260 then
(if i.val < 5258 then
(if i.val < 5257 then
[0, 0, 2, 3, 0, 0, 1, 2, 3, 0]
else
[0, 0, 2, 3, 0, 0, 1, 2, 3, 2])
else
(if i.val < 5259 then
[0, 0, 2, 3, 0, 0, 1, 3, 0, 0]
else
[0, 0, 2, 3, 0, 0, 1, 3, 2, 1]))
else
(if i.val < 5262 then
(if i.val < 5261 then
[0, 0, 2, 3, 0, 0, 2, 1, 0, 0]
else
[0, 0, 2, 3, 0, 0, 2, 1, 1, 3])
else
(if i.val < 5263 then
[0, 0, 2, 3, 0, 0, 2, 2, 1, 1]
else
[0, 0, 2, 3, 0, 0, 2, 2, 3, 2]))))
else
(if i.val < 5272 then
(if i.val < 5268 then
(if i.val < 5266 then
(if i.val < 5265 then
[0, 0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 0, 2, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 5267 then
[0, 0, 2, 3, 0, 1, 1, 0, 2, 2]
else
[0, 0, 2, 3, 0, 1, 1, 0, 3, 3]))
else
(if i.val < 5270 then
(if i.val < 5269 then
[0, 0, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 0, 2, 3, 0, 1, 1, 2, 2, 1])
else
(if i.val < 5271 then
[0, 0, 2, 3, 0, 1, 1, 2, 3, 3]
else
[0, 0, 2, 3, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 5276 then
(if i.val < 5274 then
(if i.val < 5273 then
[0, 0, 2, 3, 0, 1, 2, 2, 1, 3]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3, 0])
else
(if i.val < 5275 then
[0, 0, 2, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 2, 3, 0, 1, 2, 3, 3, 2]))
else
(if i.val < 5278 then
(if i.val < 5277 then
[0, 0, 2, 3, 0, 2, 1, 0, 3, 2]
else
[0, 0, 2, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 5279 then
[0, 0, 2, 3, 0, 2, 1, 1, 2, 3]
else
[0, 0, 2, 3, 0, 2, 2, 1, 1, 3])))))
else
(if i.val < 5296 then
(if i.val < 5288 then
(if i.val < 5284 then
(if i.val < 5282 then
(if i.val < 5281 then
[0, 0, 2, 3, 0, 2, 2, 3, 0, 1]
else
[0, 0, 2, 3, 2, 1, 0, 3, 3, 0])
else
(if i.val < 5283 then
[0, 0, 2, 3, 2, 1, 1, 0, 3, 3]
else
[0, 0, 2, 3, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 5286 then
(if i.val < 5285 then
[0, 0, 2, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 2, 3, 2, 2, 1, 3, 0, 0])
else
(if i.val < 5287 then
[0, 0, 2, 3, 2, 2, 3, 0, 0, 3]
else
[0, 0, 2, 3, 2, 2, 3, 0, 1, 2])))
else
(if i.val < 5292 then
(if i.val < 5290 then
(if i.val < 5289 then
[0, 0, 2, 3, 3, 0, 0, 1, 2, 1]
else
[0, 0, 2, 3, 3, 0, 0, 2, 1, 1])
else
(if i.val < 5291 then
[0, 0, 2, 3, 3, 0, 1, 1, 0, 3]
else
[0, 0, 2, 3, 3, 0, 1, 1, 2, 2]))
else
(if i.val < 5294 then
(if i.val < 5293 then
[0, 0, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 0, 2, 3, 3, 0, 2, 1, 0, 3])
else
(if i.val < 5295 then
[0, 0, 2, 3, 3, 0, 2, 1, 1, 3]
else
[0, 0, 2, 3, 3, 0, 2, 1, 3, 2]))))
else
(if i.val < 5304 then
(if i.val < 5300 then
(if i.val < 5298 then
(if i.val < 5297 then
[0, 0, 2, 3, 3, 0, 2, 2, 3, 3]
else
[0, 0, 2, 3, 3, 2, 1, 0, 3, 3])
else
(if i.val < 5299 then
[0, 0, 2, 3, 3, 2, 1, 1, 0, 3]
else
[0, 0, 2, 3, 3, 2, 1, 1, 2, 3]))
else
(if i.val < 5302 then
(if i.val < 5301 then
[0, 0, 3, 0, 0, 1, 1, 2, 1, 3]
else
[0, 0, 3, 0, 0, 1, 1, 2, 2, 1])
else
(if i.val < 5303 then
[0, 0, 3, 0, 0, 1, 1, 3, 2, 2]
else
[0, 0, 3, 0, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 5308 then
(if i.val < 5306 then
(if i.val < 5305 then
[0, 0, 3, 0, 0, 1, 2, 1, 3, 0]
else
[0, 0, 3, 0, 0, 1, 2, 2, 1, 3])
else
(if i.val < 5307 then
[0, 0, 3, 0, 0, 1, 2, 3, 0, 1]
else
[0, 0, 3, 0, 0, 1, 2, 3, 2, 1]))
else
(if i.val < 5310 then
(if i.val < 5309 then
[0, 0, 3, 0, 0, 1, 2, 3, 3, 2]
else
[0, 0, 3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 5311 then
[0, 0, 3, 0, 0, 2, 1, 1, 0, 0]
else
[0, 0, 3, 0, 0, 2, 1, 1, 0, 3]))))))
else
(if i.val < 5344 then
(if i.val < 5328 then
(if i.val < 5320 then
(if i.val < 5316 then
(if i.val < 5314 then
(if i.val < 5313 then
[0, 0, 3, 0, 0, 2, 1, 1, 3, 3]
else
[0, 0, 3, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 5315 then
[0, 0, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 5318 then
(if i.val < 5317 then
[0, 0, 3, 0, 0, 2, 2, 1, 3, 3]
else
[0, 0, 3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 5319 then
[0, 0, 3, 0, 0, 3, 2, 1, 0, 0]
else
[0, 0, 3, 0, 0, 3, 2, 1, 0, 3])))
else
(if i.val < 5324 then
(if i.val < 5322 then
(if i.val < 5321 then
[0, 0, 3, 0, 0, 3, 2, 2, 1, 1]
else
[0, 0, 3, 0, 0, 3, 2, 2, 3, 0])
else
(if i.val < 5323 then
[0, 0, 3, 0, 1, 1, 0, 2, 2, 1]
else
[0, 0, 3, 0, 1, 1, 0, 2, 2, 3]))
else
(if i.val < 5326 then
(if i.val < 5325 then
[0, 0, 3, 0, 1, 1, 0, 3, 2, 1]
else
[0, 0, 3, 0, 1, 1, 0, 3, 3, 0])
else
(if i.val < 5327 then
[0, 0, 3, 0, 1, 1, 0, 3, 3, 2]
else
[0, 0, 3, 0, 1, 1, 2, 2, 3, 0]))))
else
(if i.val < 5336 then
(if i.val < 5332 then
(if i.val < 5330 then
(if i.val < 5329 then
[0, 0, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 0, 3, 0, 1, 1, 2, 3, 3, 2])
else
(if i.val < 5331 then
[0, 0, 3, 0, 1, 2, 1, 1, 0, 3]
else
[0, 0, 3, 0, 1, 2, 1, 1, 3, 0]))
else
(if i.val < 5334 then
(if i.val < 5333 then
[0, 0, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 0, 3, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 5335 then
[0, 0, 3, 0, 1, 2, 3, 3, 0, 0]
else
[0, 0, 3, 0, 1, 2, 3, 3, 0, 1])))
else
(if i.val < 5340 then
(if i.val < 5338 then
(if i.val < 5337 then
[0, 0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[0, 0, 3, 0, 2, 1, 0, 3, 3, 0])
else
(if i.val < 5339 then
[0, 0, 3, 0, 2, 1, 1, 0, 3, 3]
else
[0, 0, 3, 0, 2, 1, 1, 3, 2, 2]))
else
(if i.val < 5342 then
(if i.val < 5341 then
[0, 0, 3, 0, 2, 1, 3, 3, 0, 0]
else
[0, 0, 3, 0, 2, 2, 1, 0, 0, 3])
else
(if i.val < 5343 then
[0, 0, 3, 0, 2, 2, 1, 0, 3, 2]
else
[0, 0, 3, 0, 2, 2, 1, 1, 3, 2])))))
else
(if i.val < 5360 then
(if i.val < 5352 then
(if i.val < 5348 then
(if i.val < 5346 then
(if i.val < 5345 then
[0, 0, 3, 0, 2, 2, 1, 1, 3, 3]
else
[0, 0, 3, 0, 2, 2, 3, 0, 1, 2])
else
(if i.val < 5347 then
[0, 0, 3, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 3, 0, 2, 3, 3, 2, 1, 1]))
else
(if i.val < 5350 then
(if i.val < 5349 then
[0, 0, 3, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 3, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 5351 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 3, 2, 1, 1, 0, 0, 2, 1])))
else
(if i.val < 5356 then
(if i.val < 5354 then
(if i.val < 5353 then
[0, 0, 3, 2, 1, 1, 0, 3, 3, 0]
else
[0, 0, 3, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 5355 then
[0, 0, 3, 2, 2, 1, 0, 0, 3, 0]
else
[0, 0, 3, 2, 2, 1, 0, 3, 2, 1]))
else
(if i.val < 5358 then
(if i.val < 5357 then
[0, 0, 3, 2, 2, 1, 0, 3, 3, 0]
else
[0, 0, 3, 2, 2, 1, 1, 3, 0, 1])
else
(if i.val < 5359 then
[0, 0, 3, 2, 2, 1, 3, 0, 0, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 2, 1]))))
else
(if i.val < 5368 then
(if i.val < 5364 then
(if i.val < 5362 then
(if i.val < 5361 then
[0, 0, 3, 2, 2, 3, 0, 0, 1, 1]
else
[0, 0, 3, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 5363 then
[0, 0, 3, 3, 0, 0, 1, 2, 1, 3]
else
[0, 0, 3, 3, 0, 0, 1, 2, 3, 0]))
else
(if i.val < 5366 then
(if i.val < 5365 then
[0, 0, 3, 3, 0, 0, 1, 2, 3, 3]
else
[0, 0, 3, 3, 0, 0, 2, 1, 0, 0])
else
(if i.val < 5367 then
[0, 0, 3, 3, 0, 0, 2, 1, 1, 3]
else
[0, 0, 3, 3, 0, 0, 2, 3, 3, 2])))
else
(if i.val < 5372 then
(if i.val < 5370 then
(if i.val < 5369 then
[0, 0, 3, 3, 0, 1, 1, 0, 2, 1]
else
[0, 0, 3, 3, 0, 1, 1, 0, 2, 2])
else
(if i.val < 5371 then
[0, 0, 3, 3, 0, 1, 1, 0, 3, 3]
else
[0, 0, 3, 3, 0, 1, 2, 1, 1, 3]))
else
(if i.val < 5374 then
(if i.val < 5373 then
[0, 0, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 3, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 5375 then
[0, 0, 3, 3, 0, 2, 1, 1, 0, 0]
else
[0, 0, 3, 3, 0, 2, 1, 1, 2, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0042 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5440 then
(if i.val < 5408 then
(if i.val < 5392 then
(if i.val < 5384 then
(if i.val < 5380 then
(if i.val < 5378 then
(if i.val < 5377 then
[0, 0, 3, 3, 2, 1, 0, 0, 3, 3]
else
[0, 0, 3, 3, 2, 1, 1, 0, 3, 3])
else
(if i.val < 5379 then
[0, 0, 3, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 0, 1, 2, 1, 0, 3, 2]))
else
(if i.val < 5382 then
(if i.val < 5381 then
[0, 1, 0, 0, 1, 2, 1, 1, 2, 3]
else
[0, 1, 0, 0, 1, 2, 1, 3, 0, 0])
else
(if i.val < 5383 then
[0, 1, 0, 0, 1, 2, 1, 3, 0, 1]
else
[0, 1, 0, 0, 1, 2, 1, 3, 3, 2])))
else
(if i.val < 5388 then
(if i.val < 5386 then
(if i.val < 5385 then
[0, 1, 0, 0, 1, 2, 2, 1, 0, 3]
else
[0, 1, 0, 0, 1, 2, 2, 1, 1, 3])
else
(if i.val < 5387 then
[0, 1, 0, 0, 1, 2, 2, 1, 3, 2]
else
[0, 1, 0, 0, 1, 2, 2, 1, 3, 3]))
else
(if i.val < 5390 then
(if i.val < 5389 then
[0, 1, 0, 0, 1, 2, 2, 3, 0, 0]
else
[0, 1, 0, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 5391 then
[0, 1, 0, 0, 1, 2, 2, 3, 2, 2]
else
[0, 1, 0, 0, 1, 2, 2, 3, 3, 2]))))
else
(if i.val < 5400 then
(if i.val < 5396 then
(if i.val < 5394 then
(if i.val < 5393 then
[0, 1, 0, 0, 1, 2, 3, 0, 0, 3]
else
[0, 1, 0, 0, 1, 2, 3, 0, 2, 1])
else
(if i.val < 5395 then
[0, 1, 0, 0, 1, 2, 3, 0, 2, 2]
else
[0, 1, 0, 0, 1, 2, 3, 3, 0, 1]))
else
(if i.val < 5398 then
(if i.val < 5397 then
[0, 1, 0, 0, 1, 3, 0, 0, 2, 1]
else
[0, 1, 0, 0, 1, 3, 0, 0, 2, 2])
else
(if i.val < 5399 then
[0, 1, 0, 0, 1, 3, 0, 0, 3, 2]
else
[0, 1, 0, 0, 1, 3, 0, 1, 2, 1])))
else
(if i.val < 5404 then
(if i.val < 5402 then
(if i.val < 5401 then
[0, 1, 0, 0, 1, 3, 0, 1, 2, 2]
else
[0, 1, 0, 0, 1, 3, 0, 2, 2, 1])
else
(if i.val < 5403 then
[0, 1, 0, 0, 1, 3, 2, 2, 1, 3]
else
[0, 1, 0, 0, 1, 3, 3, 0, 2, 1]))
else
(if i.val < 5406 then
(if i.val < 5405 then
[0, 1, 0, 0, 1, 3, 3, 0, 2, 2]
else
[0, 1, 0, 0, 1, 3, 3, 2, 2, 1])
else
(if i.val < 5407 then
[0, 1, 0, 0, 2, 1, 0, 0, 1, 3]
else
[0, 1, 0, 0, 2, 1, 0, 0, 3, 0])))))
else
(if i.val < 5424 then
(if i.val < 5416 then
(if i.val < 5412 then
(if i.val < 5410 then
(if i.val < 5409 then
[0, 1, 0, 0, 2, 1, 0, 3, 0, 0]
else
[0, 1, 0, 0, 2, 1, 1, 2, 3, 2])
else
(if i.val < 5411 then
[0, 1, 0, 0, 2, 1, 3, 2, 2, 1]
else
[0, 1, 0, 0, 2, 1, 3, 3, 0, 0]))
else
(if i.val < 5414 then
(if i.val < 5413 then
[0, 1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[0, 1, 0, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 5415 then
[0, 1, 0, 0, 2, 2, 3, 3, 0, 0]
else
[0, 1, 0, 0, 2, 2, 3, 3, 2, 2])))
else
(if i.val < 5420 then
(if i.val < 5418 then
(if i.val < 5417 then
[0, 1, 0, 0, 2, 3, 0, 0, 1, 1]
else
[0, 1, 0, 0, 2, 3, 0, 0, 2, 1])
else
(if i.val < 5419 then
[0, 1, 0, 0, 2, 3, 0, 0, 2, 2]
else
[0, 1, 0, 0, 2, 3, 2, 2, 3, 0]))
else
(if i.val < 5422 then
(if i.val < 5421 then
[0, 1, 0, 0, 2, 3, 3, 0, 1, 2]
else
[0, 1, 0, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 5423 then
[0, 1, 0, 0, 2, 3, 3, 0, 2, 2]
else
[0, 1, 0, 0, 3, 0, 0, 1, 1, 3]))))
else
(if i.val < 5432 then
(if i.val < 5428 then
(if i.val < 5426 then
(if i.val < 5425 then
[0, 1, 0, 0, 3, 0, 0, 2, 1, 1]
else
[0, 1, 0, 0, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5427 then
[0, 1, 0, 0, 3, 0, 0, 2, 3, 3]
else
[0, 1, 0, 0, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 5430 then
(if i.val < 5429 then
[0, 1, 0, 0, 3, 0, 0, 3, 2, 2]
else
[0, 1, 0, 0, 3, 0, 1, 1, 0, 3])
else
(if i.val < 5431 then
[0, 1, 0, 0, 3, 0, 1, 2, 1, 1]
else
[0, 1, 0, 0, 3, 0, 1, 2, 2, 1])))
else
(if i.val < 5436 then
(if i.val < 5434 then
(if i.val < 5433 then
[0, 1, 0, 0, 3, 0, 2, 1, 0, 3]
else
[0, 1, 0, 0, 3, 0, 2, 3, 3, 0])
else
(if i.val < 5435 then
[0, 1, 0, 0, 3, 2, 2, 1, 1, 3]
else
[0, 1, 0, 0, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 5438 then
(if i.val < 5437 then
[0, 1, 0, 0, 3, 3, 0, 0, 2, 1]
else
[0, 1, 0, 0, 3, 3, 0, 0, 2, 3])
else
(if i.val < 5439 then
[0, 1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[0, 1, 0, 0, 3, 3, 0, 2, 2, 1]))))))
else
(if i.val < 5472 then
(if i.val < 5456 then
(if i.val < 5448 then
(if i.val < 5444 then
(if i.val < 5442 then
(if i.val < 5441 then
[0, 1, 0, 0, 3, 3, 0, 2, 2, 3]
else
[0, 1, 0, 0, 3, 3, 0, 2, 3, 3])
else
(if i.val < 5443 then
[0, 1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[0, 1, 0, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 5446 then
(if i.val < 5445 then
[0, 1, 0, 2, 1, 1, 0, 0, 2, 1]
else
[0, 1, 0, 2, 1, 1, 0, 0, 3, 0])
else
(if i.val < 5447 then
[0, 1, 0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 1, 0, 2, 1, 1, 0, 3, 0, 0])))
else
(if i.val < 5452 then
(if i.val < 5450 then
(if i.val < 5449 then
[0, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 0, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 5451 then
[0, 1, 0, 2, 1, 1, 3, 2, 1, 1]
else
[0, 1, 0, 2, 1, 1, 3, 2, 2, 3]))
else
(if i.val < 5454 then
(if i.val < 5453 then
[0, 1, 0, 2, 2, 1, 0, 0, 3, 3]
else
[0, 1, 0, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5455 then
[0, 1, 0, 2, 2, 1, 1, 3, 0, 0]
else
[0, 1, 0, 2, 2, 1, 3, 2, 2, 1]))))
else
(if i.val < 5464 then
(if i.val < 5460 then
(if i.val < 5458 then
(if i.val < 5457 then
[0, 1, 0, 2, 2, 1, 3, 2, 2, 3]
else
[0, 1, 0, 2, 2, 1, 3, 3, 0, 0])
else
(if i.val < 5459 then
[0, 1, 0, 2, 2, 1, 3, 3, 2, 1]
else
[0, 1, 0, 2, 2, 3, 0, 0, 2, 2]))
else
(if i.val < 5462 then
(if i.val < 5461 then
[0, 1, 0, 2, 2, 3, 0, 1, 2, 2]
else
[0, 1, 0, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 5463 then
[0, 1, 0, 2, 2, 3, 2, 1, 0, 0]
else
[0, 1, 0, 2, 2, 3, 2, 1, 0, 3])))
else
(if i.val < 5468 then
(if i.val < 5466 then
(if i.val < 5465 then
[0, 1, 0, 2, 2, 3, 2, 2, 1, 3]
else
[0, 1, 0, 2, 2, 3, 3, 0, 2, 3])
else
(if i.val < 5467 then
[0, 1, 0, 2, 3, 0, 0, 2, 3, 2]
else
[0, 1, 0, 2, 3, 0, 0, 3, 2, 2]))
else
(if i.val < 5470 then
(if i.val < 5469 then
[0, 1, 0, 2, 3, 0, 1, 1, 2, 1]
else
[0, 1, 0, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 5471 then
[0, 1, 0, 2, 3, 0, 2, 1, 0, 3]
else
[0, 1, 0, 2, 3, 0, 2, 2, 3, 0])))))
else
(if i.val < 5488 then
(if i.val < 5480 then
(if i.val < 5476 then
(if i.val < 5474 then
(if i.val < 5473 then
[0, 1, 0, 2, 3, 0, 2, 2, 3, 3]
else
[0, 1, 0, 2, 3, 0, 2, 3, 3, 2])
else
(if i.val < 5475 then
[0, 1, 0, 2, 3, 2, 1, 0, 0, 3]
else
[0, 1, 0, 2, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5478 then
(if i.val < 5477 then
[0, 1, 0, 2, 3, 2, 1, 0, 3, 3]
else
[0, 1, 0, 2, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5479 then
[0, 1, 0, 2, 3, 3, 0, 0, 2, 1]
else
[0, 1, 0, 2, 3, 3, 0, 0, 2, 3])))
else
(if i.val < 5484 then
(if i.val < 5482 then
(if i.val < 5481 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 1, 0, 2, 3, 3, 0, 1, 2, 2])
else
(if i.val < 5483 then
[0, 1, 0, 2, 3, 3, 2, 1, 0, 0]
else
[0, 1, 0, 2, 3, 3, 2, 1, 0, 3]))
else
(if i.val < 5486 then
(if i.val < 5485 then
[0, 1, 0, 3, 0, 0, 1, 1, 2, 1]
else
[0, 1, 0, 3, 0, 0, 1, 3, 2, 1])
else
(if i.val < 5487 then
[0, 1, 0, 3, 0, 0, 2, 1, 1, 3]
else
[0, 1, 0, 3, 0, 0, 2, 2, 1, 1]))))
else
(if i.val < 5496 then
(if i.val < 5492 then
(if i.val < 5490 then
(if i.val < 5489 then
[0, 1, 0, 3, 0, 0, 2, 2, 3, 0]
else
[0, 1, 0, 3, 0, 0, 3, 2, 1, 1])
else
(if i.val < 5491 then
[0, 1, 0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 0, 3, 0, 1, 1, 0, 2, 1]))
else
(if i.val < 5494 then
(if i.val < 5493 then
[0, 1, 0, 3, 0, 1, 1, 0, 2, 2]
else
[0, 1, 0, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5495 then
[0, 1, 0, 3, 0, 1, 2, 2, 3, 0]
else
[0, 1, 0, 3, 0, 1, 2, 3, 0, 0])))
else
(if i.val < 5500 then
(if i.val < 5498 then
(if i.val < 5497 then
[0, 1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 0, 3, 0, 2, 1, 1, 0, 0])
else
(if i.val < 5499 then
[0, 1, 0, 3, 0, 2, 2, 1, 0, 3]
else
[0, 1, 0, 3, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 5502 then
(if i.val < 5501 then
[0, 1, 0, 3, 0, 2, 2, 3, 0, 1]
else
[0, 1, 0, 3, 0, 2, 3, 3, 0, 1])
else
(if i.val < 5503 then
[0, 1, 0, 3, 2, 1, 1, 0, 0, 3]
else
[0, 1, 0, 3, 2, 2, 1, 0, 3, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0043 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5568 then
(if i.val < 5536 then
(if i.val < 5520 then
(if i.val < 5512 then
(if i.val < 5508 then
(if i.val < 5506 then
(if i.val < 5505 then
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 3, 3, 0, 2, 2, 3, 3])
else
(if i.val < 5507 then
[0, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[0, 1, 0, 3, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5510 then
(if i.val < 5509 then
[0, 1, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 1, 1, 0, 0, 2, 1, 3, 0, 1])
else
(if i.val < 5511 then
[0, 1, 1, 0, 0, 2, 1, 3, 3, 2]
else
[0, 1, 1, 0, 0, 2, 2, 1, 0, 3])))
else
(if i.val < 5516 then
(if i.val < 5514 then
(if i.val < 5513 then
[0, 1, 1, 0, 0, 2, 2, 1, 3, 2]
else
[0, 1, 1, 0, 0, 2, 2, 1, 3, 3])
else
(if i.val < 5515 then
[0, 1, 1, 0, 0, 2, 2, 3, 3, 2]
else
[0, 1, 1, 0, 0, 2, 3, 0, 2, 2]))
else
(if i.val < 5518 then
(if i.val < 5517 then
[0, 1, 1, 0, 0, 3, 0, 0, 2, 2]
else
[0, 1, 1, 0, 0, 3, 0, 1, 2, 1])
else
(if i.val < 5519 then
[0, 1, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 1, 1, 0, 0, 3, 3, 2, 1, 1]))))
else
(if i.val < 5528 then
(if i.val < 5524 then
(if i.val < 5522 then
(if i.val < 5521 then
[0, 1, 1, 0, 2, 1, 3, 0, 0, 3]
else
[0, 1, 1, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 5523 then
[0, 1, 1, 0, 2, 2, 1, 0, 0, 3]
else
[0, 1, 1, 0, 2, 2, 1, 0, 3, 0]))
else
(if i.val < 5526 then
(if i.val < 5525 then
[0, 1, 1, 0, 2, 2, 1, 0, 3, 2]
else
[0, 1, 1, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 5527 then
[0, 1, 1, 0, 2, 2, 1, 3, 0, 1]
else
[0, 1, 1, 0, 2, 2, 1, 3, 3, 2])))
else
(if i.val < 5532 then
(if i.val < 5530 then
(if i.val < 5529 then
[0, 1, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 1, 1, 0, 2, 2, 3, 2, 2, 1])
else
(if i.val < 5531 then
[0, 1, 1, 0, 2, 2, 3, 2, 2, 3]
else
[0, 1, 1, 0, 2, 2, 3, 3, 2, 2]))
else
(if i.val < 5534 then
(if i.val < 5533 then
[0, 1, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 1, 1, 0, 2, 3, 0, 2, 1, 3])
else
(if i.val < 5535 then
[0, 1, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 1, 1, 0, 2, 3, 3, 0, 2, 2])))))
else
(if i.val < 5552 then
(if i.val < 5544 then
(if i.val < 5540 then
(if i.val < 5538 then
(if i.val < 5537 then
[0, 1, 1, 0, 3, 0, 0, 1, 1, 3]
else
[0, 1, 1, 0, 3, 0, 0, 2, 1, 1])
else
(if i.val < 5539 then
[0, 1, 1, 0, 3, 0, 0, 2, 2, 1]
else
[0, 1, 1, 0, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 5542 then
(if i.val < 5541 then
[0, 1, 1, 0, 3, 0, 1, 2, 3, 0]
else
[0, 1, 1, 0, 3, 0, 1, 2, 3, 3])
else
(if i.val < 5543 then
[0, 1, 1, 0, 3, 0, 2, 1, 0, 3]
else
[0, 1, 1, 0, 3, 0, 2, 2, 3, 0])))
else
(if i.val < 5548 then
(if i.val < 5546 then
(if i.val < 5545 then
[0, 1, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 1, 1, 0, 3, 2, 2, 1, 1, 3])
else
(if i.val < 5547 then
[0, 1, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 1, 1, 2, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 5550 then
(if i.val < 5549 then
[0, 1, 1, 2, 1, 0, 3, 0, 2, 1]
else
[0, 1, 1, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 5551 then
[0, 1, 1, 2, 1, 1, 0, 0, 3, 0]
else
[0, 1, 1, 2, 1, 1, 0, 0, 3, 3]))))
else
(if i.val < 5560 then
(if i.val < 5556 then
(if i.val < 5554 then
(if i.val < 5553 then
[0, 1, 1, 2, 1, 1, 0, 2, 1, 3]
else
[0, 1, 1, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 5555 then
[0, 1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 1, 1, 2, 1, 1, 3, 2, 1, 1]))
else
(if i.val < 5558 then
(if i.val < 5557 then
[0, 1, 1, 2, 1, 1, 3, 2, 2, 3]
else
[0, 1, 1, 2, 1, 1, 3, 3, 2, 2])
else
(if i.val < 5559 then
[0, 1, 1, 2, 1, 3, 0, 0, 3, 2]
else
[0, 1, 1, 2, 1, 3, 0, 1, 2, 2])))
else
(if i.val < 5564 then
(if i.val < 5562 then
(if i.val < 5561 then
[0, 1, 1, 2, 1, 3, 0, 2, 2, 3]
else
[0, 1, 1, 2, 1, 3, 2, 2, 1, 1])
else
(if i.val < 5563 then
[0, 1, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 1, 1, 2, 2, 1, 3, 2, 1, 1]))
else
(if i.val < 5566 then
(if i.val < 5565 then
[0, 1, 1, 2, 2, 3, 0, 1, 2, 3]
else
[0, 1, 1, 2, 2, 3, 2, 2, 1, 1])
else
(if i.val < 5567 then
[0, 1, 1, 2, 2, 3, 3, 0, 2, 3]
else
[0, 1, 1, 2, 3, 0, 0, 3, 2, 2]))))))
else
(if i.val < 5600 then
(if i.val < 5584 then
(if i.val < 5576 then
(if i.val < 5572 then
(if i.val < 5570 then
(if i.val < 5569 then
[0, 1, 1, 2, 3, 0, 1, 1, 2, 2]
else
[0, 1, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 5571 then
[0, 1, 1, 2, 3, 0, 2, 1, 1, 3]
else
[0, 1, 1, 2, 3, 2, 1, 0, 0, 3]))
else
(if i.val < 5574 then
(if i.val < 5573 then
[0, 1, 1, 2, 3, 3, 0, 0, 1, 1]
else
[0, 1, 1, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 5575 then
[0, 1, 1, 2, 3, 3, 0, 1, 2, 1]
else
[0, 1, 1, 2, 3, 3, 0, 2, 3, 3])))
else
(if i.val < 5580 then
(if i.val < 5578 then
(if i.val < 5577 then
[0, 1, 1, 2, 3, 3, 2, 1, 0, 0]
else
[0, 1, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 5579 then
[0, 1, 1, 3, 0, 0, 1, 3, 2, 1]
else
[0, 1, 1, 3, 0, 0, 3, 2, 1, 1]))
else
(if i.val < 5582 then
(if i.val < 5581 then
[0, 1, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 1, 1, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 5583 then
[0, 1, 1, 3, 0, 1, 1, 0, 2, 2]
else
[0, 1, 1, 3, 0, 1, 2, 1, 1, 3]))))
else
(if i.val < 5592 then
(if i.val < 5588 then
(if i.val < 5586 then
(if i.val < 5585 then
[0, 1, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 1, 1, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 5587 then
[0, 1, 1, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 1, 3, 0, 2, 1, 0, 3, 2]))
else
(if i.val < 5590 then
(if i.val < 5589 then
[0, 1, 1, 3, 0, 2, 2, 1, 0, 3]
else
[0, 1, 1, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 5591 then
[0, 1, 1, 3, 0, 2, 2, 3, 0, 1]
else
[0, 1, 1, 3, 2, 2, 1, 1, 3, 2])))
else
(if i.val < 5596 then
(if i.val < 5594 then
(if i.val < 5593 then
[0, 1, 1, 3, 3, 0, 1, 2, 2, 3]
else
[0, 1, 1, 3, 3, 0, 1, 2, 3, 0])
else
(if i.val < 5595 then
[0, 1, 1, 3, 3, 0, 2, 3, 3, 2]
else
[0, 1, 2, 1, 0, 0, 1, 3, 0, 0]))
else
(if i.val < 5598 then
(if i.val < 5597 then
[0, 1, 2, 1, 0, 0, 1, 3, 3, 2]
else
[0, 1, 2, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 5599 then
[0, 1, 2, 1, 0, 3, 2, 1, 0, 0]
else
[0, 1, 2, 1, 0, 3, 2, 1, 0, 3])))))
else
(if i.val < 5616 then
(if i.val < 5608 then
(if i.val < 5604 then
(if i.val < 5602 then
(if i.val < 5601 then
[0, 1, 2, 1, 0, 3, 2, 2, 3, 0]
else
[0, 1, 2, 1, 0, 3, 3, 0, 2, 2])
else
(if i.val < 5603 then
[0, 1, 2, 1, 1, 0, 0, 3, 0, 0]
else
[0, 1, 2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 5606 then
(if i.val < 5605 then
[0, 1, 2, 1, 1, 0, 2, 1, 3, 2]
else
[0, 1, 2, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 5607 then
[0, 1, 2, 1, 1, 0, 2, 3, 3, 2]
else
[0, 1, 2, 1, 1, 2, 3, 2, 2, 3])))
else
(if i.val < 5612 then
(if i.val < 5610 then
(if i.val < 5609 then
[0, 1, 2, 1, 1, 3, 0, 1, 2, 2]
else
[0, 1, 2, 1, 1, 3, 0, 1, 2, 3])
else
(if i.val < 5611 then
[0, 1, 2, 1, 3, 0, 0, 1, 2, 3]
else
[0, 1, 2, 1, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 5614 then
(if i.val < 5613 then
[0, 1, 2, 1, 3, 0, 0, 2, 2, 3]
else
[0, 1, 2, 1, 3, 0, 0, 3, 2, 1])
else
(if i.val < 5615 then
[0, 1, 2, 1, 3, 0, 0, 3, 2, 2]
else
[0, 1, 2, 1, 3, 0, 2, 2, 3, 3]))))
else
(if i.val < 5624 then
(if i.val < 5620 then
(if i.val < 5618 then
(if i.val < 5617 then
[0, 1, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 1, 2, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5619 then
[0, 1, 2, 1, 3, 3, 0, 0, 2, 1]
else
[0, 1, 2, 1, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 5622 then
(if i.val < 5621 then
[0, 1, 2, 1, 3, 3, 0, 2, 1, 3]
else
[0, 1, 2, 1, 3, 3, 0, 2, 2, 3])
else
(if i.val < 5623 then
[0, 1, 2, 1, 3, 3, 0, 2, 3, 3]
else
[0, 1, 2, 1, 3, 3, 2, 1, 0, 0])))
else
(if i.val < 5628 then
(if i.val < 5626 then
(if i.val < 5625 then
[0, 1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 2, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 5627 then
[0, 1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 1, 2, 2, 1, 0, 3, 0, 2, 2]))
else
(if i.val < 5630 then
(if i.val < 5629 then
[0, 1, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 1, 2, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 5631 then
[0, 1, 2, 2, 1, 1, 3, 0, 1, 2]
else
[0, 1, 2, 2, 1, 1, 3, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0044 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5696 then
(if i.val < 5664 then
(if i.val < 5648 then
(if i.val < 5640 then
(if i.val < 5636 then
(if i.val < 5634 then
(if i.val < 5633 then
[0, 1, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 1, 2, 2, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5635 then
[0, 1, 2, 2, 3, 2, 1, 0, 3, 3]
else
[0, 1, 2, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 5638 then
(if i.val < 5637 then
[0, 1, 2, 3, 0, 0, 1, 2, 1, 3]
else
[0, 1, 2, 3, 0, 0, 1, 2, 3, 0])
else
(if i.val < 5639 then
[0, 1, 2, 3, 0, 0, 1, 2, 3, 2]
else
[0, 1, 2, 3, 0, 0, 1, 3, 0, 0])))
else
(if i.val < 5644 then
(if i.val < 5642 then
(if i.val < 5641 then
[0, 1, 2, 3, 0, 0, 2, 2, 1, 1]
else
[0, 1, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 5643 then
[0, 1, 2, 3, 0, 1, 1, 0, 2, 1]
else
[0, 1, 2, 3, 0, 1, 1, 0, 2, 2]))
else
(if i.val < 5646 then
(if i.val < 5645 then
[0, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 1, 2, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5647 then
[0, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 1, 2, 3, 0, 1, 2, 3, 0, 0]))))
else
(if i.val < 5656 then
(if i.val < 5652 then
(if i.val < 5650 then
(if i.val < 5649 then
[0, 1, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 2, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 5651 then
[0, 1, 2, 3, 2, 1, 0, 3, 3, 0]
else
[0, 1, 2, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 5654 then
(if i.val < 5653 then
[0, 1, 2, 3, 3, 0, 0, 1, 2, 1]
else
[0, 1, 2, 3, 3, 0, 1, 1, 2, 2])
else
(if i.val < 5655 then
[0, 1, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 2, 3, 3, 0, 2, 1, 1, 3])))
else
(if i.val < 5660 then
(if i.val < 5658 then
(if i.val < 5657 then
[0, 1, 2, 3, 3, 2, 1, 1, 2, 3]
else
[0, 1, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 5659 then
[0, 1, 3, 0, 0, 1, 2, 1, 1, 3]
else
[0, 1, 3, 0, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 5662 then
(if i.val < 5661 then
[0, 1, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 1, 3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 5663 then
[0, 1, 3, 0, 0, 3, 2, 2, 3, 0]
else
[0, 1, 3, 0, 1, 1, 0, 2, 2, 3])))))
else
(if i.val < 5680 then
(if i.val < 5672 then
(if i.val < 5668 then
(if i.val < 5666 then
(if i.val < 5665 then
[0, 1, 3, 0, 1, 1, 0, 3, 3, 0]
else
[0, 1, 3, 0, 1, 1, 0, 3, 3, 2])
else
(if i.val < 5667 then
[0, 1, 3, 0, 1, 1, 2, 2, 3, 0]
else
[0, 1, 3, 0, 1, 2, 1, 1, 0, 3]))
else
(if i.val < 5670 then
(if i.val < 5669 then
[0, 1, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 1, 3, 0, 2, 2, 1, 0, 3, 2])
else
(if i.val < 5671 then
[0, 1, 3, 0, 2, 3, 3, 0, 1, 2]
else
[0, 1, 3, 2, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 5676 then
(if i.val < 5674 then
(if i.val < 5673 then
[0, 1, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 1, 3, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 5675 then
[0, 1, 3, 2, 2, 1, 0, 0, 3, 0]
else
[0, 1, 3, 2, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 5678 then
(if i.val < 5677 then
[0, 1, 3, 2, 2, 1, 3, 0, 0, 1]
else
[0, 1, 3, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 5679 then
[0, 1, 3, 2, 2, 3, 0, 1, 2, 3]
else
[0, 1, 3, 3, 0, 0, 1, 2, 1, 3]))))
else
(if i.val < 5688 then
(if i.val < 5684 then
(if i.val < 5682 then
(if i.val < 5681 then
[0, 1, 3, 3, 0, 0, 1, 2, 3, 0]
else
[0, 1, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 5683 then
[0, 1, 3, 3, 0, 1, 1, 0, 2, 1]
else
[0, 1, 3, 3, 0, 1, 1, 0, 2, 2]))
else
(if i.val < 5686 then
(if i.val < 5685 then
[0, 1, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 1, 3, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 5687 then
[0, 1, 3, 3, 0, 2, 1, 1, 0, 0]
else
[0, 1, 3, 3, 0, 2, 1, 1, 2, 3])))
else
(if i.val < 5692 then
(if i.val < 5690 then
(if i.val < 5689 then
[0, 2, 1, 0, 0, 1, 2, 2, 3, 2]
else
[0, 2, 1, 0, 0, 1, 2, 3, 0, 0])
else
(if i.val < 5691 then
[0, 2, 1, 0, 0, 1, 2, 3, 0, 1]
else
[0, 2, 1, 0, 0, 1, 2, 3, 3, 0]))
else
(if i.val < 5694 then
(if i.val < 5693 then
[0, 2, 1, 0, 0, 1, 3, 2, 1, 1]
else
[0, 2, 1, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 5695 then
[0, 2, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 2, 1, 0, 3, 0, 0, 1, 2, 1]))))))
else
(if i.val < 5728 then
(if i.val < 5712 then
(if i.val < 5704 then
(if i.val < 5700 then
(if i.val < 5698 then
(if i.val < 5697 then
[0, 2, 1, 0, 3, 0, 2, 1, 0, 3]
else
[0, 2, 1, 0, 3, 0, 2, 2, 1, 3])
else
(if i.val < 5699 then
[0, 2, 1, 0, 3, 2, 1, 1, 0, 0]
else
[0, 2, 1, 0, 3, 2, 2, 1, 0, 3]))
else
(if i.val < 5702 then
(if i.val < 5701 then
[0, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 2, 1, 0, 3, 2, 2, 1, 3, 2])
else
(if i.val < 5703 then
[0, 2, 1, 0, 3, 3, 0, 2, 2, 3]
else
[0, 2, 1, 0, 3, 3, 2, 1, 0, 3])))
else
(if i.val < 5708 then
(if i.val < 5706 then
(if i.val < 5705 then
[0, 2, 1, 1, 0, 0, 2, 1, 1, 3]
else
[0, 2, 1, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 5707 then
[0, 2, 1, 1, 0, 2, 3, 0, 2, 1]
else
[0, 2, 1, 1, 0, 2, 3, 2, 2, 3]))
else
(if i.val < 5710 then
(if i.val < 5709 then
[0, 2, 1, 1, 0, 3, 0, 1, 2, 1]
else
[0, 2, 1, 1, 0, 3, 2, 2, 3, 0])
else
(if i.val < 5711 then
[0, 2, 1, 1, 2, 3, 0, 0, 2, 2]
else
[0, 2, 1, 1, 2, 3, 0, 1, 2, 2]))))
else
(if i.val < 5720 then
(if i.val < 5716 then
(if i.val < 5714 then
(if i.val < 5713 then
[0, 2, 1, 1, 2, 3, 0, 2, 2, 1]
else
[0, 2, 1, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 5715 then
[0, 2, 1, 1, 3, 0, 0, 1, 2, 1]
else
[0, 2, 1, 1, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 5718 then
(if i.val < 5717 then
[0, 2, 1, 1, 3, 0, 0, 3, 2, 1]
else
[0, 2, 1, 1, 3, 0, 1, 2, 2, 3])
else
(if i.val < 5719 then
[0, 2, 1, 1, 3, 0, 2, 1, 0, 3]
else
[0, 2, 1, 1, 3, 0, 2, 2, 3, 0])))
else
(if i.val < 5724 then
(if i.val < 5722 then
(if i.val < 5721 then
[0, 2, 1, 1, 3, 3, 0, 0, 2, 1]
else
[0, 2, 1, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 5723 then
[0, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 2, 1, 3, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 5726 then
(if i.val < 5725 then
[0, 2, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 2, 1, 3, 0, 2, 2, 3, 0, 1])
else
(if i.val < 5727 then
[0, 2, 1, 3, 2, 1, 0, 3, 3, 0]
else
[0, 2, 1, 3, 3, 0, 0, 1, 2, 1])))))
else
(if i.val < 5744 then
(if i.val < 5736 then
(if i.val < 5732 then
(if i.val < 5730 then
(if i.val < 5729 then
[0, 2, 2, 1, 0, 0, 3, 2, 2, 1]
else
[0, 2, 2, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 5731 then
[0, 2, 2, 1, 0, 3, 0, 2, 2, 1]
else
[0, 2, 2, 1, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 5734 then
(if i.val < 5733 then
[0, 2, 2, 1, 1, 0, 3, 0, 1, 2]
else
[0, 2, 2, 1, 3, 0, 0, 1, 2, 1])
else
(if i.val < 5735 then
[0, 2, 2, 1, 3, 0, 0, 3, 2, 1]
else
[0, 2, 2, 1, 3, 2, 2, 1, 3, 2])))
else
(if i.val < 5740 then
(if i.val < 5738 then
(if i.val < 5737 then
[0, 2, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 2, 2, 1, 3, 3, 0, 2, 3, 3])
else
(if i.val < 5739 then
[0, 2, 2, 3, 0, 0, 2, 1, 1, 3]
else
[0, 2, 2, 3, 0, 0, 2, 2, 1, 1]))
else
(if i.val < 5742 then
(if i.val < 5741 then
[0, 2, 2, 3, 0, 1, 1, 0, 2, 1]
else
[0, 2, 2, 3, 0, 1, 1, 0, 3, 3])
else
(if i.val < 5743 then
[0, 2, 2, 3, 0, 1, 2, 3, 0, 0]
else
[0, 2, 2, 3, 0, 2, 1, 1, 0, 3]))))
else
(if i.val < 5752 then
(if i.val < 5748 then
(if i.val < 5746 then
(if i.val < 5745 then
[0, 2, 2, 3, 0, 2, 2, 1, 1, 3]
else
[0, 2, 2, 3, 2, 1, 0, 3, 3, 0])
else
(if i.val < 5747 then
[0, 2, 2, 3, 2, 2, 1, 1, 3, 2]
else
[0, 2, 3, 0, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 5750 then
(if i.val < 5749 then
[0, 2, 3, 0, 1, 1, 0, 3, 3, 2]
else
[0, 2, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 5751 then
[0, 2, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 2, 3, 0, 1, 2, 2, 3, 0, 1])))
else
(if i.val < 5756 then
(if i.val < 5754 then
(if i.val < 5753 then
[0, 2, 3, 0, 1, 2, 3, 3, 0, 0]
else
[0, 2, 3, 0, 1, 2, 3, 3, 0, 1])
else
(if i.val < 5755 then
[0, 2, 3, 0, 2, 1, 1, 0, 3, 3]
else
[0, 2, 3, 0, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 5758 then
(if i.val < 5757 then
[0, 2, 3, 2, 1, 0, 0, 1, 2, 3]
else
[0, 2, 3, 2, 1, 1, 0, 3, 3, 0])
else
(if i.val < 5759 then
[0, 2, 3, 2, 2, 3, 0, 0, 1, 1]
else
[0, 2, 3, 3, 0, 0, 1, 2, 1, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0045 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5824 then
(if i.val < 5792 then
(if i.val < 5776 then
(if i.val < 5768 then
(if i.val < 5764 then
(if i.val < 5762 then
(if i.val < 5761 then
[0, 2, 3, 3, 0, 0, 2, 1, 1, 3]
else
[0, 2, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5763 then
[0, 2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 2, 3, 3, 2, 1, 1, 0, 3, 3]))
else
(if i.val < 5766 then
(if i.val < 5765 then
[0, 3, 0, 0, 1, 1, 2, 3, 0, 1]
else
[0, 3, 0, 0, 1, 2, 3, 0, 1, 2])
else
(if i.val < 5767 then
[0, 3, 0, 0, 1, 3, 0, 0, 2, 1]
else
[0, 3, 0, 0, 2, 1, 0, 0, 3, 3])))
else
(if i.val < 5772 then
(if i.val < 5770 then
(if i.val < 5769 then
[0, 3, 0, 0, 2, 1, 0, 3, 0, 0]
else
[0, 3, 0, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 5771 then
[0, 3, 0, 0, 2, 1, 3, 3, 0, 0]
else
[0, 3, 0, 0, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 5774 then
(if i.val < 5773 then
[0, 3, 0, 0, 2, 2, 1, 1, 3, 2]
else
[0, 3, 0, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 5775 then
[0, 3, 0, 1, 1, 0, 3, 2, 2, 1]
else
[0, 3, 0, 1, 1, 0, 3, 3, 2, 2]))))
else
(if i.val < 5784 then
(if i.val < 5780 then
(if i.val < 5778 then
(if i.val < 5777 then
[0, 3, 0, 1, 2, 1, 1, 0, 0, 3]
else
[0, 3, 0, 1, 2, 1, 3, 3, 0, 0])
else
(if i.val < 5779 then
[0, 3, 0, 2, 1, 0, 3, 0, 0, 3]
else
[0, 3, 0, 2, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 5782 then
(if i.val < 5781 then
[0, 3, 0, 2, 1, 1, 3, 3, 0, 1]
else
[0, 3, 0, 2, 2, 1, 1, 3, 3, 2])
else
(if i.val < 5783 then
[0, 3, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 3, 0, 2, 3, 3, 0, 2, 1, 1])))
else
(if i.val < 5788 then
(if i.val < 5786 then
(if i.val < 5785 then
[0, 3, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 3, 2, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 5787 then
[0, 3, 2, 1, 0, 3, 2, 2, 3, 0]
else
[0, 3, 2, 1, 1, 0, 2, 1, 1, 3]))
else
(if i.val < 5790 then
(if i.val < 5789 then
[0, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 3, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 5791 then
[0, 3, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 3, 2, 2, 1, 3, 0, 0, 2, 3])))))
else
(if i.val < 5808 then
(if i.val < 5800 then
(if i.val < 5796 then
(if i.val < 5794 then
(if i.val < 5793 then
[0, 3, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 3, 3, 0, 2, 1, 3, 3, 0, 0])
else
(if i.val < 5795 then
[0, 3, 3, 2, 1, 0, 3, 2, 1, 1]
else
[0, 3, 3, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 5798 then
(if i.val < 5797 then
[1, 0, 0, 1, 2, 1, 1, 2, 3, 2]
else
[1, 0, 0, 1, 2, 1, 3, 3, 2, 2])
else
(if i.val < 5799 then
[1, 0, 0, 1, 2, 2, 1, 3, 3, 2]
else
[1, 0, 0, 1, 2, 2, 3, 3, 0, 0])))
else
(if i.val < 5804 then
(if i.val < 5802 then
(if i.val < 5801 then
[1, 0, 0, 1, 2, 3, 3, 0, 1, 2]
else
[1, 0, 0, 1, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5803 then
[1, 0, 0, 1, 3, 0, 0, 3, 2, 1]
else
[1, 0, 0, 1, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 5806 then
(if i.val < 5805 then
[1, 0, 0, 1, 3, 3, 0, 1, 2, 1]
else
[1, 0, 0, 1, 3, 3, 0, 2, 3, 3])
else
(if i.val < 5807 then
[1, 0, 0, 2, 1, 1, 2, 3, 0, 0]
else
[1, 0, 0, 2, 1, 1, 2, 3, 0, 1]))))
else
(if i.val < 5816 then
(if i.val < 5812 then
(if i.val < 5810 then
(if i.val < 5809 then
[1, 0, 0, 2, 3, 0, 0, 1, 3, 2]
else
[1, 0, 0, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 5811 then
[1, 0, 0, 2, 3, 3, 0, 0, 2, 1]
else
[1, 0, 0, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 5814 then
(if i.val < 5813 then
[1, 0, 0, 3, 0, 1, 2, 3, 3, 2]
else
[1, 0, 0, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 5815 then
[1, 0, 0, 3, 2, 2, 1, 0, 3, 2]
else
[1, 0, 0, 3, 2, 2, 1, 1, 3, 2])))
else
(if i.val < 5820 then
(if i.val < 5818 then
(if i.val < 5817 then
[1, 0, 0, 3, 3, 0, 2, 1, 0, 3]
else
[1, 0, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 5819 then
[1, 0, 2, 1, 1, 0, 0, 3, 0, 0]
else
[1, 0, 2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 5822 then
(if i.val < 5821 then
[1, 0, 2, 1, 1, 0, 0, 3, 3, 2]
else
[1, 0, 2, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5823 then
[1, 0, 2, 2, 3, 0, 1, 2, 2, 1]
else
[1, 0, 2, 2, 3, 2, 2, 1, 1, 3]))))))
else
(if i.val < 5856 then
(if i.val < 5840 then
(if i.val < 5832 then
(if i.val < 5828 then
(if i.val < 5826 then
(if i.val < 5825 then
[1, 0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[1, 0, 2, 3, 0, 1, 2, 3, 3, 2])
else
(if i.val < 5827 then
[1, 0, 2, 3, 3, 0, 1, 2, 3, 0]
else
[1, 0, 3, 0, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 5830 then
(if i.val < 5829 then
[1, 0, 3, 0, 0, 1, 3, 2, 2, 1]
else
[1, 0, 3, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 5831 then
[1, 0, 3, 0, 0, 2, 2, 1, 0, 3]
else
[1, 0, 3, 0, 1, 1, 2, 2, 3, 0])))
else
(if i.val < 5836 then
(if i.val < 5834 then
(if i.val < 5833 then
[1, 0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[1, 0, 3, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 5835 then
[1, 0, 3, 0, 2, 2, 1, 1, 3, 3]
else
[1, 0, 3, 2, 1, 1, 0, 0, 2, 1]))
else
(if i.val < 5838 then
(if i.val < 5837 then
[1, 0, 3, 2, 2, 1, 0, 0, 3, 0]
else
[1, 0, 3, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 5839 then
[1, 0, 3, 2, 2, 1, 3, 0, 2, 1]
else
[1, 0, 3, 2, 2, 3, 0, 0, 1, 1]))))
else
(if i.val < 5848 then
(if i.val < 5844 then
(if i.val < 5842 then
(if i.val < 5841 then
[1, 1, 0, 0, 2, 2, 1, 3, 3, 2]
else
[1, 1, 0, 0, 3, 2, 2, 1, 1, 3])
else
(if i.val < 5843 then
[1, 1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[1, 1, 0, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 5846 then
(if i.val < 5845 then
[1, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[1, 1, 0, 2, 2, 1, 3, 2, 2, 1])
else
(if i.val < 5847 then
[1, 1, 0, 2, 3, 3, 0, 0, 2, 3]
else
[1, 1, 0, 3, 0, 0, 1, 3, 2, 1])))
else
(if i.val < 5852 then
(if i.val < 5850 then
(if i.val < 5849 then
[1, 1, 0, 3, 0, 1, 2, 1, 1, 3]
else
[1, 1, 0, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 5851 then
[1, 1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[1, 1, 0, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 5854 then
(if i.val < 5853 then
[1, 1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[1, 1, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 5855 then
[1, 1, 2, 2, 1, 1, 3, 2, 1, 1]
else
[1, 1, 2, 2, 1, 3, 0, 0, 2, 1])))))
else
(if i.val < 5872 then
(if i.val < 5864 then
(if i.val < 5860 then
(if i.val < 5858 then
(if i.val < 5857 then
[1, 1, 2, 3, 0, 0, 2, 3, 3, 2]
else
[1, 1, 2, 3, 3, 0, 1, 1, 2, 2])
else
(if i.val < 5859 then
[1, 1, 3, 0, 0, 1, 2, 1, 1, 3]
else
[1, 1, 3, 0, 1, 1, 2, 2, 3, 0]))
else
(if i.val < 5862 then
(if i.val < 5861 then
[1, 1, 3, 0, 2, 2, 1, 0, 3, 2]
else
[1, 1, 3, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 5863 then
[1, 2, 1, 0, 0, 1, 2, 3, 0, 0]
else
[1, 2, 1, 0, 3, 0, 2, 1, 0, 3])))
else
(if i.val < 5868 then
(if i.val < 5866 then
(if i.val < 5865 then
[1, 2, 1, 1, 3, 0, 0, 2, 2, 1]
else
[1, 2, 1, 1, 3, 3, 0, 0, 2, 1])
else
(if i.val < 5867 then
[1, 2, 1, 3, 0, 0, 1, 2, 1, 3]
else
[1, 2, 2, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 5870 then
(if i.val < 5869 then
[1, 2, 2, 1, 0, 3, 2, 2, 1, 3]
else
[1, 2, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 5871 then
[1, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[1, 3, 3, 2, 1, 0, 3, 2, 1, 1]))))
else
(if i.val < 5880 then
(if i.val < 5876 then
(if i.val < 5874 then
(if i.val < 5873 then
[1, 3, 3, 2, 1, 0, 3, 2, 2, 3]
else
[2, 1, 0, 0, 1, 3, 2, 2, 1, 3])
else
(if i.val < 5875 then
[2, 1, 0, 3, 0, 1, 1, 0, 2, 1]
else
[2, 1, 0, 3, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 5878 then
(if i.val < 5877 then
[2, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[2, 1, 1, 0, 0, 2, 1, 3, 3, 2])
else
(if i.val < 5879 then
[2, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[2, 3, 0, 2, 1, 1, 2, 3, 0, 1])))
else
(if i.val < 5884 then
(if i.val < 5882 then
(if i.val < 5881 then
[3, 0, 0, 1, 2, 3, 0, 1, 2, 2]
else
[3, 0, 1, 1, 0, 2, 2, 3, 3, 2])
else
(if i.val < 5883 then
[3, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 1, 2, 1, 0, 3, 2]))
else
(if i.val < 5886 then
(if i.val < 5885 then
[0, 0, 1, 0, 0, 1, 2, 1, 1, 2, 3]
else
[0, 0, 1, 0, 0, 1, 2, 1, 3, 0, 0])
else
(if i.val < 5887 then
[0, 0, 1, 0, 0, 1, 2, 1, 3, 0, 1]
else
[0, 0, 1, 0, 0, 1, 2, 1, 3, 3, 2])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0046 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 5952 then
(if i.val < 5920 then
(if i.val < 5904 then
(if i.val < 5896 then
(if i.val < 5892 then
(if i.val < 5890 then
(if i.val < 5889 then
[0, 0, 1, 0, 0, 1, 2, 2, 1, 0, 3]
else
[0, 0, 1, 0, 0, 1, 2, 2, 1, 1, 3])
else
(if i.val < 5891 then
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3, 2]
else
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3, 3]))
else
(if i.val < 5894 then
(if i.val < 5893 then
[0, 0, 1, 0, 0, 1, 2, 2, 3, 0, 0]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3, 0, 1])
else
(if i.val < 5895 then
[0, 0, 1, 0, 0, 1, 2, 2, 3, 2, 2]
else
[0, 0, 1, 0, 0, 1, 2, 2, 3, 3, 2])))
else
(if i.val < 5900 then
(if i.val < 5898 then
(if i.val < 5897 then
[0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 3]
else
[0, 0, 1, 0, 0, 1, 2, 3, 0, 2, 1])
else
(if i.val < 5899 then
[0, 0, 1, 0, 0, 1, 2, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 1, 2, 3, 3, 0, 1]))
else
(if i.val < 5902 then
(if i.val < 5901 then
[0, 0, 1, 0, 0, 1, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 0, 1, 3, 0, 0, 2, 2])
else
(if i.val < 5903 then
[0, 0, 1, 0, 0, 1, 3, 0, 0, 3, 2]
else
[0, 0, 1, 0, 0, 1, 3, 0, 1, 2, 1]))))
else
(if i.val < 5912 then
(if i.val < 5908 then
(if i.val < 5906 then
(if i.val < 5905 then
[0, 0, 1, 0, 0, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 0, 1, 3, 0, 2, 2, 1])
else
(if i.val < 5907 then
[0, 0, 1, 0, 0, 1, 3, 2, 2, 1, 3]
else
[0, 0, 1, 0, 0, 1, 3, 3, 0, 2, 1]))
else
(if i.val < 5910 then
(if i.val < 5909 then
[0, 0, 1, 0, 0, 1, 3, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 1, 3, 3, 2, 2, 1])
else
(if i.val < 5911 then
[0, 0, 1, 0, 0, 2, 1, 0, 0, 1, 3]
else
[0, 0, 1, 0, 0, 2, 1, 0, 0, 3, 0])))
else
(if i.val < 5916 then
(if i.val < 5914 then
(if i.val < 5913 then
[0, 0, 1, 0, 0, 2, 1, 0, 3, 0, 0]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 2])
else
(if i.val < 5915 then
[0, 0, 1, 0, 0, 2, 1, 3, 2, 2, 1]
else
[0, 0, 1, 0, 0, 2, 1, 3, 3, 0, 0]))
else
(if i.val < 5918 then
(if i.val < 5917 then
[0, 0, 1, 0, 0, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 0, 0, 2, 2, 1, 3, 3, 2])
else
(if i.val < 5919 then
[0, 0, 1, 0, 0, 2, 2, 3, 3, 0, 0]
else
[0, 0, 1, 0, 0, 2, 2, 3, 3, 2, 2])))))
else
(if i.val < 5936 then
(if i.val < 5928 then
(if i.val < 5924 then
(if i.val < 5922 then
(if i.val < 5921 then
[0, 0, 1, 0, 0, 2, 3, 0, 0, 1, 1]
else
[0, 0, 1, 0, 0, 2, 3, 0, 0, 2, 1])
else
(if i.val < 5923 then
[0, 0, 1, 0, 0, 2, 3, 0, 0, 2, 2]
else
[0, 0, 1, 0, 0, 2, 3, 2, 2, 3, 0]))
else
(if i.val < 5926 then
(if i.val < 5925 then
[0, 0, 1, 0, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 0, 0, 2, 3, 3, 0, 2, 1])
else
(if i.val < 5927 then
[0, 0, 1, 0, 0, 2, 3, 3, 0, 2, 2]
else
[0, 0, 1, 0, 0, 3, 0, 0, 1, 1, 3])))
else
(if i.val < 5932 then
(if i.val < 5930 then
(if i.val < 5929 then
[0, 0, 1, 0, 0, 3, 0, 0, 2, 1, 1]
else
[0, 0, 1, 0, 0, 3, 0, 0, 2, 2, 1])
else
(if i.val < 5931 then
[0, 0, 1, 0, 0, 3, 0, 0, 2, 3, 3]
else
[0, 0, 1, 0, 0, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 5934 then
(if i.val < 5933 then
[0, 0, 1, 0, 0, 3, 0, 0, 3, 2, 2]
else
[0, 0, 1, 0, 0, 3, 0, 1, 1, 0, 3])
else
(if i.val < 5935 then
[0, 0, 1, 0, 0, 3, 0, 1, 2, 1, 1]
else
[0, 0, 1, 0, 0, 3, 0, 1, 2, 2, 1]))))
else
(if i.val < 5944 then
(if i.val < 5940 then
(if i.val < 5938 then
(if i.val < 5937 then
[0, 0, 1, 0, 0, 3, 0, 2, 1, 0, 3]
else
[0, 0, 1, 0, 0, 3, 0, 2, 3, 3, 0])
else
(if i.val < 5939 then
[0, 0, 1, 0, 0, 3, 2, 2, 1, 1, 3]
else
[0, 0, 1, 0, 0, 3, 2, 2, 3, 0, 1]))
else
(if i.val < 5942 then
(if i.val < 5941 then
[0, 0, 1, 0, 0, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 0, 0, 2, 3])
else
(if i.val < 5943 then
[0, 0, 1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2, 2, 1])))
else
(if i.val < 5948 then
(if i.val < 5946 then
(if i.val < 5945 then
[0, 0, 1, 0, 0, 3, 3, 0, 2, 2, 3]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2, 3, 3])
else
(if i.val < 5947 then
[0, 0, 1, 0, 0, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 0, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 5950 then
(if i.val < 5949 then
[0, 0, 1, 0, 2, 1, 1, 0, 0, 2, 1]
else
[0, 0, 1, 0, 2, 1, 1, 0, 0, 3, 0])
else
(if i.val < 5951 then
[0, 0, 1, 0, 2, 1, 1, 0, 2, 1, 3]
else
[0, 0, 1, 0, 2, 1, 1, 0, 3, 0, 0]))))))
else
(if i.val < 5984 then
(if i.val < 5968 then
(if i.val < 5960 then
(if i.val < 5956 then
(if i.val < 5954 then
(if i.val < 5953 then
[0, 0, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 0, 1, 0, 2, 1, 1, 2, 3, 0, 1])
else
(if i.val < 5955 then
[0, 0, 1, 0, 2, 1, 1, 3, 2, 1, 1]
else
[0, 0, 1, 0, 2, 1, 1, 3, 2, 2, 3]))
else
(if i.val < 5958 then
(if i.val < 5957 then
[0, 0, 1, 0, 2, 2, 1, 0, 0, 3, 3]
else
[0, 0, 1, 0, 2, 2, 1, 1, 0, 3, 2])
else
(if i.val < 5959 then
[0, 0, 1, 0, 2, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 0, 2, 2, 1, 3, 2, 2, 1])))
else
(if i.val < 5964 then
(if i.val < 5962 then
(if i.val < 5961 then
[0, 0, 1, 0, 2, 2, 1, 3, 2, 2, 3]
else
[0, 0, 1, 0, 2, 2, 1, 3, 3, 0, 0])
else
(if i.val < 5963 then
[0, 0, 1, 0, 2, 2, 1, 3, 3, 2, 1]
else
[0, 0, 1, 0, 2, 2, 3, 0, 0, 2, 2]))
else
(if i.val < 5966 then
(if i.val < 5965 then
[0, 0, 1, 0, 2, 2, 3, 0, 1, 2, 2]
else
[0, 0, 1, 0, 2, 2, 3, 0, 1, 2, 3])
else
(if i.val < 5967 then
[0, 0, 1, 0, 2, 2, 3, 2, 1, 0, 0]
else
[0, 0, 1, 0, 2, 2, 3, 2, 1, 0, 3]))))
else
(if i.val < 5976 then
(if i.val < 5972 then
(if i.val < 5970 then
(if i.val < 5969 then
[0, 0, 1, 0, 2, 2, 3, 2, 2, 1, 3]
else
[0, 0, 1, 0, 2, 2, 3, 3, 0, 2, 3])
else
(if i.val < 5971 then
[0, 0, 1, 0, 2, 3, 0, 0, 2, 3, 2]
else
[0, 0, 1, 0, 2, 3, 0, 0, 3, 2, 2]))
else
(if i.val < 5974 then
(if i.val < 5973 then
[0, 0, 1, 0, 2, 3, 0, 1, 1, 2, 1]
else
[0, 0, 1, 0, 2, 3, 0, 1, 2, 3, 3])
else
(if i.val < 5975 then
[0, 0, 1, 0, 2, 3, 0, 2, 1, 0, 3]
else
[0, 0, 1, 0, 2, 3, 0, 2, 2, 3, 0])))
else
(if i.val < 5980 then
(if i.val < 5978 then
(if i.val < 5977 then
[0, 0, 1, 0, 2, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 0, 2, 3, 0, 2, 3, 3, 2])
else
(if i.val < 5979 then
[0, 0, 1, 0, 2, 3, 2, 1, 0, 0, 3]
else
[0, 0, 1, 0, 2, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 5982 then
(if i.val < 5981 then
[0, 0, 1, 0, 2, 3, 2, 1, 0, 3, 3]
else
[0, 0, 1, 0, 2, 3, 2, 2, 3, 0, 0])
else
(if i.val < 5983 then
[0, 0, 1, 0, 2, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 2, 3, 3, 0, 0, 2, 3])))))
else
(if i.val < 6000 then
(if i.val < 5992 then
(if i.val < 5988 then
(if i.val < 5986 then
(if i.val < 5985 then
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2, 2])
else
(if i.val < 5987 then
[0, 0, 1, 0, 2, 3, 3, 2, 1, 0, 0]
else
[0, 0, 1, 0, 2, 3, 3, 2, 1, 0, 3]))
else
(if i.val < 5990 then
(if i.val < 5989 then
[0, 0, 1, 0, 3, 0, 0, 1, 1, 2, 1]
else
[0, 0, 1, 0, 3, 0, 0, 1, 3, 2, 1])
else
(if i.val < 5991 then
[0, 0, 1, 0, 3, 0, 0, 2, 1, 1, 3]
else
[0, 0, 1, 0, 3, 0, 0, 2, 2, 1, 1])))
else
(if i.val < 5996 then
(if i.val < 5994 then
(if i.val < 5993 then
[0, 0, 1, 0, 3, 0, 0, 2, 2, 3, 0]
else
[0, 0, 1, 0, 3, 0, 0, 3, 2, 1, 1])
else
(if i.val < 5995 then
[0, 0, 1, 0, 3, 0, 0, 3, 2, 2, 1]
else
[0, 0, 1, 0, 3, 0, 1, 1, 0, 2, 1]))
else
(if i.val < 5998 then
(if i.val < 5997 then
[0, 0, 1, 0, 3, 0, 1, 1, 0, 2, 2]
else
[0, 0, 1, 0, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 5999 then
[0, 0, 1, 0, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 1, 0, 3, 0, 1, 2, 3, 0, 0]))))
else
(if i.val < 6008 then
(if i.val < 6004 then
(if i.val < 6002 then
(if i.val < 6001 then
[0, 0, 1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 0, 3, 0, 2, 1, 1, 0, 0])
else
(if i.val < 6003 then
[0, 0, 1, 0, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 1, 0, 3, 0, 2, 2, 1, 1, 3]))
else
(if i.val < 6006 then
(if i.val < 6005 then
[0, 0, 1, 0, 3, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 0, 3, 0, 2, 3, 3, 0, 1])
else
(if i.val < 6007 then
[0, 0, 1, 0, 3, 2, 1, 1, 0, 0, 3]
else
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 0])))
else
(if i.val < 6012 then
(if i.val < 6010 then
(if i.val < 6009 then
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 0, 3, 3, 0, 2, 2, 3, 3])
else
(if i.val < 6011 then
[0, 0, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[0, 0, 1, 0, 3, 3, 2, 1, 0, 3, 2]))
else
(if i.val < 6014 then
(if i.val < 6013 then
[0, 0, 1, 1, 0, 0, 2, 1, 1, 2, 3]
else
[0, 0, 1, 1, 0, 0, 2, 1, 3, 0, 1])
else
(if i.val < 6015 then
[0, 0, 1, 1, 0, 0, 2, 1, 3, 3, 2]
else
[0, 0, 1, 1, 0, 0, 2, 2, 1, 0, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0047 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 6080 then
(if i.val < 6048 then
(if i.val < 6032 then
(if i.val < 6024 then
(if i.val < 6020 then
(if i.val < 6018 then
(if i.val < 6017 then
[0, 0, 1, 1, 0, 0, 2, 2, 1, 3, 2]
else
[0, 0, 1, 1, 0, 0, 2, 2, 1, 3, 3])
else
(if i.val < 6019 then
[0, 0, 1, 1, 0, 0, 2, 2, 3, 3, 2]
else
[0, 0, 1, 1, 0, 0, 2, 3, 0, 2, 2]))
else
(if i.val < 6022 then
(if i.val < 6021 then
[0, 0, 1, 1, 0, 0, 3, 0, 0, 2, 2]
else
[0, 0, 1, 1, 0, 0, 3, 0, 1, 2, 1])
else
(if i.val < 6023 then
[0, 0, 1, 1, 0, 0, 3, 3, 0, 2, 1]
else
[0, 0, 1, 1, 0, 0, 3, 3, 2, 1, 1])))
else
(if i.val < 6028 then
(if i.val < 6026 then
(if i.val < 6025 then
[0, 0, 1, 1, 0, 2, 1, 3, 0, 0, 3]
else
[0, 0, 1, 1, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 6027 then
[0, 0, 1, 1, 0, 2, 2, 1, 0, 0, 3]
else
[0, 0, 1, 1, 0, 2, 2, 1, 0, 3, 0]))
else
(if i.val < 6030 then
(if i.val < 6029 then
[0, 0, 1, 1, 0, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 1, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 6031 then
[0, 0, 1, 1, 0, 2, 2, 1, 3, 0, 1]
else
[0, 0, 1, 1, 0, 2, 2, 1, 3, 3, 2]))))
else
(if i.val < 6040 then
(if i.val < 6036 then
(if i.val < 6034 then
(if i.val < 6033 then
[0, 0, 1, 1, 0, 2, 2, 3, 0, 1, 2]
else
[0, 0, 1, 1, 0, 2, 2, 3, 2, 2, 1])
else
(if i.val < 6035 then
[0, 0, 1, 1, 0, 2, 2, 3, 2, 2, 3]
else
[0, 0, 1, 1, 0, 2, 2, 3, 3, 2, 2]))
else
(if i.val < 6038 then
(if i.val < 6037 then
[0, 0, 1, 1, 0, 2, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 2, 3, 0, 2, 1, 3])
else
(if i.val < 6039 then
[0, 0, 1, 1, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 1, 0, 2, 3, 3, 0, 2, 2])))
else
(if i.val < 6044 then
(if i.val < 6042 then
(if i.val < 6041 then
[0, 0, 1, 1, 0, 3, 0, 0, 1, 1, 3]
else
[0, 0, 1, 1, 0, 3, 0, 0, 2, 1, 1])
else
(if i.val < 6043 then
[0, 0, 1, 1, 0, 3, 0, 0, 2, 2, 1]
else
[0, 0, 1, 1, 0, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 6046 then
(if i.val < 6045 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 3, 0]
else
[0, 0, 1, 1, 0, 3, 0, 1, 2, 3, 3])
else
(if i.val < 6047 then
[0, 0, 1, 1, 0, 3, 0, 2, 1, 0, 3]
else
[0, 0, 1, 1, 0, 3, 0, 2, 2, 3, 0])))))
else
(if i.val < 6064 then
(if i.val < 6056 then
(if i.val < 6052 then
(if i.val < 6050 then
(if i.val < 6049 then
[0, 0, 1, 1, 0, 3, 0, 2, 2, 3, 3]
else
[0, 0, 1, 1, 0, 3, 2, 2, 1, 1, 3])
else
(if i.val < 6051 then
[0, 0, 1, 1, 0, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 2, 1, 0, 3, 0, 1, 2]))
else
(if i.val < 6054 then
(if i.val < 6053 then
[0, 0, 1, 1, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 1, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 6055 then
[0, 0, 1, 1, 2, 1, 1, 0, 0, 3, 0]
else
[0, 0, 1, 1, 2, 1, 1, 0, 0, 3, 3])))
else
(if i.val < 6060 then
(if i.val < 6058 then
(if i.val < 6057 then
[0, 0, 1, 1, 2, 1, 1, 0, 2, 1, 3]
else
[0, 0, 1, 1, 2, 1, 1, 2, 3, 0, 0])
else
(if i.val < 6059 then
[0, 0, 1, 1, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 1, 1, 2, 1, 1, 3, 2, 1, 1]))
else
(if i.val < 6062 then
(if i.val < 6061 then
[0, 0, 1, 1, 2, 1, 1, 3, 2, 2, 3]
else
[0, 0, 1, 1, 2, 1, 1, 3, 3, 2, 2])
else
(if i.val < 6063 then
[0, 0, 1, 1, 2, 1, 3, 0, 0, 3, 2]
else
[0, 0, 1, 1, 2, 1, 3, 0, 1, 2, 2]))))
else
(if i.val < 6072 then
(if i.val < 6068 then
(if i.val < 6066 then
(if i.val < 6065 then
[0, 0, 1, 1, 2, 1, 3, 0, 2, 2, 3]
else
[0, 0, 1, 1, 2, 1, 3, 2, 2, 1, 1])
else
(if i.val < 6067 then
[0, 0, 1, 1, 2, 2, 1, 1, 3, 0, 0]
else
[0, 0, 1, 1, 2, 2, 1, 3, 2, 1, 1]))
else
(if i.val < 6070 then
(if i.val < 6069 then
[0, 0, 1, 1, 2, 2, 3, 0, 1, 2, 3]
else
[0, 0, 1, 1, 2, 2, 3, 2, 2, 1, 1])
else
(if i.val < 6071 then
[0, 0, 1, 1, 2, 2, 3, 3, 0, 2, 3]
else
[0, 0, 1, 1, 2, 3, 0, 0, 3, 2, 2])))
else
(if i.val < 6076 then
(if i.val < 6074 then
(if i.val < 6073 then
[0, 0, 1, 1, 2, 3, 0, 1, 1, 2, 2]
else
[0, 0, 1, 1, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 6075 then
[0, 0, 1, 1, 2, 3, 0, 2, 1, 1, 3]
else
[0, 0, 1, 1, 2, 3, 2, 1, 0, 0, 3]))
else
(if i.val < 6078 then
(if i.val < 6077 then
[0, 0, 1, 1, 2, 3, 3, 0, 0, 1, 1]
else
[0, 0, 1, 1, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 6079 then
[0, 0, 1, 1, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 2, 3, 3, 0, 2, 3, 3]))))))
else
(if i.val < 6112 then
(if i.val < 6096 then
(if i.val < 6088 then
(if i.val < 6084 then
(if i.val < 6082 then
(if i.val < 6081 then
[0, 0, 1, 1, 2, 3, 3, 2, 1, 0, 0]
else
[0, 0, 1, 1, 2, 3, 3, 2, 1, 0, 3])
else
(if i.val < 6083 then
[0, 0, 1, 1, 3, 0, 0, 1, 3, 2, 1]
else
[0, 0, 1, 1, 3, 0, 0, 3, 2, 1, 1]))
else
(if i.val < 6086 then
(if i.val < 6085 then
[0, 0, 1, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 0, 1, 1, 3, 0, 1, 1, 0, 2, 1])
else
(if i.val < 6087 then
[0, 0, 1, 1, 3, 0, 1, 1, 0, 2, 2]
else
[0, 0, 1, 1, 3, 0, 1, 2, 1, 1, 3])))
else
(if i.val < 6092 then
(if i.val < 6090 then
(if i.val < 6089 then
[0, 0, 1, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 1, 1, 3, 0, 1, 2, 3, 3, 0])
else
(if i.val < 6091 then
[0, 0, 1, 1, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 1, 3, 0, 2, 1, 0, 3, 2]))
else
(if i.val < 6094 then
(if i.val < 6093 then
[0, 0, 1, 1, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 1, 1, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 6095 then
[0, 0, 1, 1, 3, 0, 2, 2, 3, 0, 1]
else
[0, 0, 1, 1, 3, 2, 2, 1, 1, 3, 2]))))
else
(if i.val < 6104 then
(if i.val < 6100 then
(if i.val < 6098 then
(if i.val < 6097 then
[0, 0, 1, 1, 3, 3, 0, 1, 2, 2, 3]
else
[0, 0, 1, 1, 3, 3, 0, 1, 2, 3, 0])
else
(if i.val < 6099 then
[0, 0, 1, 1, 3, 3, 0, 2, 3, 3, 2]
else
[0, 0, 1, 2, 1, 0, 0, 1, 3, 0, 0]))
else
(if i.val < 6102 then
(if i.val < 6101 then
[0, 0, 1, 2, 1, 0, 0, 1, 3, 3, 2]
else
[0, 0, 1, 2, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 6103 then
[0, 0, 1, 2, 1, 0, 3, 2, 1, 0, 0]
else
[0, 0, 1, 2, 1, 0, 3, 2, 1, 0, 3])))
else
(if i.val < 6108 then
(if i.val < 6106 then
(if i.val < 6105 then
[0, 0, 1, 2, 1, 0, 3, 2, 2, 3, 0]
else
[0, 0, 1, 2, 1, 0, 3, 3, 0, 2, 2])
else
(if i.val < 6107 then
[0, 0, 1, 2, 1, 1, 0, 0, 3, 0, 0]
else
[0, 0, 1, 2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 6110 then
(if i.val < 6109 then
[0, 0, 1, 2, 1, 1, 0, 2, 1, 3, 2]
else
[0, 0, 1, 2, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 6111 then
[0, 0, 1, 2, 1, 1, 0, 2, 3, 3, 2]
else
[0, 0, 1, 2, 1, 1, 2, 3, 2, 2, 3])))))
else
(if i.val < 6128 then
(if i.val < 6120 then
(if i.val < 6116 then
(if i.val < 6114 then
(if i.val < 6113 then
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2, 2]
else
[0, 0, 1, 2, 1, 1, 3, 0, 1, 2, 3])
else
(if i.val < 6115 then
[0, 0, 1, 2, 1, 3, 0, 0, 1, 2, 3]
else
[0, 0, 1, 2, 1, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 6118 then
(if i.val < 6117 then
[0, 0, 1, 2, 1, 3, 0, 0, 2, 2, 3]
else
[0, 0, 1, 2, 1, 3, 0, 0, 3, 2, 1])
else
(if i.val < 6119 then
[0, 0, 1, 2, 1, 3, 0, 0, 3, 2, 2]
else
[0, 0, 1, 2, 1, 3, 0, 2, 2, 3, 3])))
else
(if i.val < 6124 then
(if i.val < 6122 then
(if i.val < 6121 then
[0, 0, 1, 2, 1, 3, 2, 2, 1, 1, 3]
else
[0, 0, 1, 2, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 6123 then
[0, 0, 1, 2, 1, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 1, 3, 3, 0, 1, 2, 3]))
else
(if i.val < 6126 then
(if i.val < 6125 then
[0, 0, 1, 2, 1, 3, 3, 0, 2, 1, 3]
else
[0, 0, 1, 2, 1, 3, 3, 0, 2, 2, 3])
else
(if i.val < 6127 then
[0, 0, 1, 2, 1, 3, 3, 0, 2, 3, 3]
else
[0, 0, 1, 2, 1, 3, 3, 2, 1, 0, 0]))))
else
(if i.val < 6136 then
(if i.val < 6132 then
(if i.val < 6130 then
(if i.val < 6129 then
[0, 0, 1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 2, 2, 1, 0, 0, 3, 3, 2])
else
(if i.val < 6131 then
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 0, 2, 2]))
else
(if i.val < 6134 then
(if i.val < 6133 then
[0, 0, 1, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 6135 then
[0, 0, 1, 2, 2, 1, 1, 3, 0, 1, 2]
else
[0, 0, 1, 2, 2, 1, 1, 3, 2, 1, 1])))
else
(if i.val < 6140 then
(if i.val < 6138 then
(if i.val < 6137 then
[0, 0, 1, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 2, 3, 0, 0, 2, 2, 1])
else
(if i.val < 6139 then
[0, 0, 1, 2, 2, 3, 2, 1, 0, 3, 3]
else
[0, 0, 1, 2, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 6142 then
(if i.val < 6141 then
[0, 0, 1, 2, 3, 0, 0, 1, 2, 1, 3]
else
[0, 0, 1, 2, 3, 0, 0, 1, 2, 3, 0])
else
(if i.val < 6143 then
[0, 0, 1, 2, 3, 0, 0, 1, 2, 3, 2]
else
[0, 0, 1, 2, 3, 0, 0, 1, 3, 0, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0048 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 6208 then
(if i.val < 6176 then
(if i.val < 6160 then
(if i.val < 6152 then
(if i.val < 6148 then
(if i.val < 6146 then
(if i.val < 6145 then
[0, 0, 1, 2, 3, 0, 0, 2, 2, 1, 1]
else
[0, 0, 1, 2, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 6147 then
[0, 0, 1, 2, 3, 0, 1, 1, 0, 2, 1]
else
[0, 0, 1, 2, 3, 0, 1, 1, 0, 2, 2]))
else
(if i.val < 6150 then
(if i.val < 6149 then
[0, 0, 1, 2, 3, 0, 1, 1, 2, 1, 1]
else
[0, 0, 1, 2, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6151 then
[0, 0, 1, 2, 3, 0, 1, 2, 2, 3, 0]
else
[0, 0, 1, 2, 3, 0, 1, 2, 3, 0, 0])))
else
(if i.val < 6156 then
(if i.val < 6154 then
(if i.val < 6153 then
[0, 0, 1, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 2, 3, 0, 2, 2, 1, 1, 3])
else
(if i.val < 6155 then
[0, 0, 1, 2, 3, 2, 1, 0, 3, 3, 0]
else
[0, 0, 1, 2, 3, 2, 2, 1, 3, 0, 0]))
else
(if i.val < 6158 then
(if i.val < 6157 then
[0, 0, 1, 2, 3, 3, 0, 0, 1, 2, 1]
else
[0, 0, 1, 2, 3, 3, 0, 1, 1, 2, 2])
else
(if i.val < 6159 then
[0, 0, 1, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 0, 1, 2, 3, 3, 0, 2, 1, 1, 3]))))
else
(if i.val < 6168 then
(if i.val < 6164 then
(if i.val < 6162 then
(if i.val < 6161 then
[0, 0, 1, 2, 3, 3, 2, 1, 1, 2, 3]
else
[0, 0, 1, 3, 0, 0, 1, 1, 2, 1, 3])
else
(if i.val < 6163 then
[0, 0, 1, 3, 0, 0, 1, 2, 1, 1, 3]
else
[0, 0, 1, 3, 0, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 6166 then
(if i.val < 6165 then
[0, 0, 1, 3, 0, 0, 2, 2, 1, 0, 0]
else
[0, 0, 1, 3, 0, 0, 2, 2, 3, 3, 2])
else
(if i.val < 6167 then
[0, 0, 1, 3, 0, 0, 3, 2, 2, 3, 0]
else
[0, 0, 1, 3, 0, 1, 1, 0, 2, 2, 3])))
else
(if i.val < 6172 then
(if i.val < 6170 then
(if i.val < 6169 then
[0, 0, 1, 3, 0, 1, 1, 0, 3, 3, 0]
else
[0, 0, 1, 3, 0, 1, 1, 0, 3, 3, 2])
else
(if i.val < 6171 then
[0, 0, 1, 3, 0, 1, 1, 2, 2, 3, 0]
else
[0, 0, 1, 3, 0, 1, 2, 1, 1, 0, 3]))
else
(if i.val < 6174 then
(if i.val < 6173 then
[0, 0, 1, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 0, 1, 3, 0, 2, 2, 1, 0, 3, 2])
else
(if i.val < 6175 then
[0, 0, 1, 3, 0, 2, 3, 3, 0, 1, 2]
else
[0, 0, 1, 3, 2, 1, 0, 3, 2, 1, 1])))))
else
(if i.val < 6192 then
(if i.val < 6184 then
(if i.val < 6180 then
(if i.val < 6178 then
(if i.val < 6177 then
[0, 0, 1, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 1, 3, 2, 1, 1, 0, 0, 2, 1])
else
(if i.val < 6179 then
[0, 0, 1, 3, 2, 2, 1, 0, 0, 3, 0]
else
[0, 0, 1, 3, 2, 2, 1, 1, 3, 0, 1]))
else
(if i.val < 6182 then
(if i.val < 6181 then
[0, 0, 1, 3, 2, 2, 1, 3, 0, 0, 1]
else
[0, 0, 1, 3, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 6183 then
[0, 0, 1, 3, 2, 2, 3, 0, 1, 2, 3]
else
[0, 0, 1, 3, 3, 0, 0, 1, 2, 1, 3])))
else
(if i.val < 6188 then
(if i.val < 6186 then
(if i.val < 6185 then
[0, 0, 1, 3, 3, 0, 0, 1, 2, 3, 0]
else
[0, 0, 1, 3, 3, 0, 0, 2, 3, 3, 2])
else
(if i.val < 6187 then
[0, 0, 1, 3, 3, 0, 1, 1, 0, 2, 1]
else
[0, 0, 1, 3, 3, 0, 1, 1, 0, 2, 2]))
else
(if i.val < 6190 then
(if i.val < 6189 then
[0, 0, 1, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 1, 3, 3, 0, 2, 1, 0, 3, 2])
else
(if i.val < 6191 then
[0, 0, 1, 3, 3, 0, 2, 1, 1, 0, 0]
else
[0, 0, 1, 3, 3, 0, 2, 1, 1, 2, 3]))))
else
(if i.val < 6200 then
(if i.val < 6196 then
(if i.val < 6194 then
(if i.val < 6193 then
[0, 0, 2, 1, 0, 0, 1, 2, 2, 3, 2]
else
[0, 0, 2, 1, 0, 0, 1, 2, 3, 0, 0])
else
(if i.val < 6195 then
[0, 0, 2, 1, 0, 0, 1, 2, 3, 0, 1]
else
[0, 0, 2, 1, 0, 0, 1, 2, 3, 3, 0]))
else
(if i.val < 6198 then
(if i.val < 6197 then
[0, 0, 2, 1, 0, 0, 1, 3, 2, 1, 1]
else
[0, 0, 2, 1, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 6199 then
[0, 0, 2, 1, 0, 0, 3, 3, 2, 2, 1]
else
[0, 0, 2, 1, 0, 3, 0, 0, 1, 2, 1])))
else
(if i.val < 6204 then
(if i.val < 6202 then
(if i.val < 6201 then
[0, 0, 2, 1, 0, 3, 0, 2, 1, 0, 3]
else
[0, 0, 2, 1, 0, 3, 0, 2, 2, 1, 3])
else
(if i.val < 6203 then
[0, 0, 2, 1, 0, 3, 2, 1, 1, 0, 0]
else
[0, 0, 2, 1, 0, 3, 2, 2, 1, 0, 3]))
else
(if i.val < 6206 then
(if i.val < 6205 then
[0, 0, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 0, 2, 1, 0, 3, 2, 2, 1, 3, 2])
else
(if i.val < 6207 then
[0, 0, 2, 1, 0, 3, 3, 0, 2, 2, 3]
else
[0, 0, 2, 1, 0, 3, 3, 2, 1, 0, 3]))))))
else
(if i.val < 6240 then
(if i.val < 6224 then
(if i.val < 6216 then
(if i.val < 6212 then
(if i.val < 6210 then
(if i.val < 6209 then
[0, 0, 2, 1, 1, 0, 0, 2, 1, 1, 3]
else
[0, 0, 2, 1, 1, 0, 0, 3, 3, 2, 2])
else
(if i.val < 6211 then
[0, 0, 2, 1, 1, 0, 2, 3, 0, 2, 1]
else
[0, 0, 2, 1, 1, 0, 2, 3, 2, 2, 3]))
else
(if i.val < 6214 then
(if i.val < 6213 then
[0, 0, 2, 1, 1, 0, 3, 0, 1, 2, 1]
else
[0, 0, 2, 1, 1, 0, 3, 2, 2, 3, 0])
else
(if i.val < 6215 then
[0, 0, 2, 1, 1, 2, 3, 0, 0, 2, 2]
else
[0, 0, 2, 1, 1, 2, 3, 0, 1, 2, 2])))
else
(if i.val < 6220 then
(if i.val < 6218 then
(if i.val < 6217 then
[0, 0, 2, 1, 1, 2, 3, 0, 2, 2, 1]
else
[0, 0, 2, 1, 1, 2, 3, 3, 0, 2, 3])
else
(if i.val < 6219 then
[0, 0, 2, 1, 1, 3, 0, 0, 1, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 0, 2, 2, 1]))
else
(if i.val < 6222 then
(if i.val < 6221 then
[0, 0, 2, 1, 1, 3, 0, 0, 3, 2, 1]
else
[0, 0, 2, 1, 1, 3, 0, 1, 2, 2, 3])
else
(if i.val < 6223 then
[0, 0, 2, 1, 1, 3, 0, 2, 1, 0, 3]
else
[0, 0, 2, 1, 1, 3, 0, 2, 2, 3, 0]))))
else
(if i.val < 6232 then
(if i.val < 6228 then
(if i.val < 6226 then
(if i.val < 6225 then
[0, 0, 2, 1, 1, 3, 3, 0, 0, 2, 1]
else
[0, 0, 2, 1, 3, 0, 0, 1, 2, 1, 3])
else
(if i.val < 6227 then
[0, 0, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 0, 2, 1, 3, 0, 1, 2, 2, 1, 3]))
else
(if i.val < 6230 then
(if i.val < 6229 then
[0, 0, 2, 1, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 2, 1, 3, 0, 2, 2, 3, 0, 1])
else
(if i.val < 6231 then
[0, 0, 2, 1, 3, 2, 1, 0, 3, 3, 0]
else
[0, 0, 2, 1, 3, 3, 0, 0, 1, 2, 1])))
else
(if i.val < 6236 then
(if i.val < 6234 then
(if i.val < 6233 then
[0, 0, 2, 2, 1, 0, 0, 3, 2, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 0, 1, 2, 1])
else
(if i.val < 6235 then
[0, 0, 2, 2, 1, 0, 3, 0, 2, 2, 1]
else
[0, 0, 2, 2, 1, 0, 3, 2, 2, 1, 3]))
else
(if i.val < 6238 then
(if i.val < 6237 then
[0, 0, 2, 2, 1, 1, 0, 3, 0, 1, 2]
else
[0, 0, 2, 2, 1, 3, 0, 0, 1, 2, 1])
else
(if i.val < 6239 then
[0, 0, 2, 2, 1, 3, 0, 0, 3, 2, 1]
else
[0, 0, 2, 2, 1, 3, 2, 2, 1, 3, 2])))))
else
(if i.val < 6256 then
(if i.val < 6248 then
(if i.val < 6244 then
(if i.val < 6242 then
(if i.val < 6241 then
[0, 0, 2, 2, 1, 3, 3, 0, 1, 2, 3]
else
[0, 0, 2, 2, 1, 3, 3, 0, 2, 3, 3])
else
(if i.val < 6243 then
[0, 0, 2, 2, 3, 0, 0, 2, 1, 1, 3]
else
[0, 0, 2, 2, 3, 0, 0, 2, 2, 1, 1]))
else
(if i.val < 6246 then
(if i.val < 6245 then
[0, 0, 2, 2, 3, 0, 1, 1, 0, 2, 1]
else
[0, 0, 2, 2, 3, 0, 1, 1, 0, 3, 3])
else
(if i.val < 6247 then
[0, 0, 2, 2, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 2, 2, 3, 0, 2, 1, 1, 0, 3])))
else
(if i.val < 6252 then
(if i.val < 6250 then
(if i.val < 6249 then
[0, 0, 2, 2, 3, 0, 2, 2, 1, 1, 3]
else
[0, 0, 2, 2, 3, 2, 1, 0, 3, 3, 0])
else
(if i.val < 6251 then
[0, 0, 2, 2, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 2, 3, 0, 0, 3, 2, 1, 0, 0]))
else
(if i.val < 6254 then
(if i.val < 6253 then
[0, 0, 2, 3, 0, 1, 1, 0, 3, 3, 2]
else
[0, 0, 2, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 6255 then
[0, 0, 2, 3, 0, 1, 2, 2, 1, 0, 0]
else
[0, 0, 2, 3, 0, 1, 2, 2, 3, 0, 1]))))
else
(if i.val < 6264 then
(if i.val < 6260 then
(if i.val < 6258 then
(if i.val < 6257 then
[0, 0, 2, 3, 0, 1, 2, 3, 3, 0, 0]
else
[0, 0, 2, 3, 0, 1, 2, 3, 3, 0, 1])
else
(if i.val < 6259 then
[0, 0, 2, 3, 0, 2, 1, 1, 0, 3, 3]
else
[0, 0, 2, 3, 0, 2, 2, 1, 0, 0, 3]))
else
(if i.val < 6262 then
(if i.val < 6261 then
[0, 0, 2, 3, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 2, 3, 2, 1, 1, 0, 3, 3, 0])
else
(if i.val < 6263 then
[0, 0, 2, 3, 2, 2, 3, 0, 0, 1, 1]
else
[0, 0, 2, 3, 3, 0, 0, 1, 2, 1, 3])))
else
(if i.val < 6268 then
(if i.val < 6266 then
(if i.val < 6265 then
[0, 0, 2, 3, 3, 0, 0, 2, 1, 1, 3]
else
[0, 0, 2, 3, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6267 then
[0, 0, 2, 3, 3, 0, 1, 2, 3, 0, 0]
else
[0, 0, 2, 3, 3, 2, 1, 1, 0, 3, 3]))
else
(if i.val < 6270 then
(if i.val < 6269 then
[0, 0, 3, 0, 0, 1, 1, 2, 3, 0, 1]
else
[0, 0, 3, 0, 0, 1, 2, 3, 0, 1, 2])
else
(if i.val < 6271 then
[0, 0, 3, 0, 0, 1, 3, 0, 0, 2, 1]
else
[0, 0, 3, 0, 0, 2, 1, 0, 0, 3, 3])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0049 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 6336 then
(if i.val < 6304 then
(if i.val < 6288 then
(if i.val < 6280 then
(if i.val < 6276 then
(if i.val < 6274 then
(if i.val < 6273 then
[0, 0, 3, 0, 0, 2, 1, 0, 3, 0, 0]
else
[0, 0, 3, 0, 0, 2, 1, 3, 2, 2, 3])
else
(if i.val < 6275 then
[0, 0, 3, 0, 0, 2, 1, 3, 3, 0, 0]
else
[0, 0, 3, 0, 0, 2, 2, 1, 0, 3, 2]))
else
(if i.val < 6278 then
(if i.val < 6277 then
[0, 0, 3, 0, 0, 2, 2, 1, 1, 3, 2]
else
[0, 0, 3, 0, 1, 1, 0, 2, 1, 3, 3])
else
(if i.val < 6279 then
[0, 0, 3, 0, 1, 1, 0, 3, 2, 2, 1]
else
[0, 0, 3, 0, 1, 1, 0, 3, 3, 2, 2])))
else
(if i.val < 6284 then
(if i.val < 6282 then
(if i.val < 6281 then
[0, 0, 3, 0, 1, 2, 1, 1, 0, 0, 3]
else
[0, 0, 3, 0, 1, 2, 1, 3, 3, 0, 0])
else
(if i.val < 6283 then
[0, 0, 3, 0, 2, 1, 0, 3, 0, 0, 3]
else
[0, 0, 3, 0, 2, 1, 1, 2, 3, 0, 1]))
else
(if i.val < 6286 then
(if i.val < 6285 then
[0, 0, 3, 0, 2, 1, 1, 3, 3, 0, 1]
else
[0, 0, 3, 0, 2, 2, 1, 1, 3, 3, 2])
else
(if i.val < 6287 then
[0, 0, 3, 0, 2, 3, 3, 0, 1, 2, 1]
else
[0, 0, 3, 0, 2, 3, 3, 0, 2, 1, 1]))))
else
(if i.val < 6296 then
(if i.val < 6292 then
(if i.val < 6290 then
(if i.val < 6289 then
[0, 0, 3, 2, 1, 0, 0, 1, 2, 2, 3]
else
[0, 0, 3, 2, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 6291 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 3, 0]
else
[0, 0, 3, 2, 1, 1, 0, 2, 1, 1, 3]))
else
(if i.val < 6294 then
(if i.val < 6293 then
[0, 0, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 3, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 6295 then
[0, 0, 3, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 0, 3, 2, 2, 1, 3, 0, 0, 2, 3])))
else
(if i.val < 6300 then
(if i.val < 6298 then
(if i.val < 6297 then
[0, 0, 3, 3, 0, 1, 1, 2, 2, 3, 3]
else
[0, 0, 3, 3, 0, 2, 1, 3, 3, 0, 0])
else
(if i.val < 6299 then
[0, 0, 3, 3, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 3, 3, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 6302 then
(if i.val < 6301 then
[0, 1, 0, 0, 1, 2, 1, 1, 2, 3, 2]
else
[0, 1, 0, 0, 1, 2, 1, 3, 3, 2, 2])
else
(if i.val < 6303 then
[0, 1, 0, 0, 1, 2, 2, 1, 3, 3, 2]
else
[0, 1, 0, 0, 1, 2, 2, 3, 3, 0, 0])))))
else
(if i.val < 6320 then
(if i.val < 6312 then
(if i.val < 6308 then
(if i.val < 6306 then
(if i.val < 6305 then
[0, 1, 0, 0, 1, 2, 3, 3, 0, 1, 2]
else
[0, 1, 0, 0, 1, 3, 0, 0, 2, 2, 1])
else
(if i.val < 6307 then
[0, 1, 0, 0, 1, 3, 0, 0, 3, 2, 1]
else
[0, 1, 0, 0, 1, 3, 0, 2, 1, 0, 3]))
else
(if i.val < 6310 then
(if i.val < 6309 then
[0, 1, 0, 0, 1, 3, 3, 0, 1, 2, 1]
else
[0, 1, 0, 0, 1, 3, 3, 0, 2, 3, 3])
else
(if i.val < 6311 then
[0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 1])))
else
(if i.val < 6316 then
(if i.val < 6314 then
(if i.val < 6313 then
[0, 1, 0, 0, 2, 3, 0, 0, 1, 3, 2]
else
[0, 1, 0, 0, 2, 3, 0, 1, 2, 2, 1])
else
(if i.val < 6315 then
[0, 1, 0, 0, 2, 3, 3, 0, 0, 2, 1]
else
[0, 1, 0, 0, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 6318 then
(if i.val < 6317 then
[0, 1, 0, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 0, 0, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 6319 then
[0, 1, 0, 0, 3, 2, 2, 1, 0, 3, 2]
else
[0, 1, 0, 0, 3, 2, 2, 1, 1, 3, 2]))))
else
(if i.val < 6328 then
(if i.val < 6324 then
(if i.val < 6322 then
(if i.val < 6321 then
[0, 1, 0, 0, 3, 3, 0, 2, 1, 0, 3]
else
[0, 1, 0, 0, 3, 3, 0, 2, 3, 3, 2])
else
(if i.val < 6323 then
[0, 1, 0, 2, 1, 1, 0, 0, 3, 0, 0]
else
[0, 1, 0, 2, 1, 1, 0, 0, 3, 0, 1]))
else
(if i.val < 6326 then
(if i.val < 6325 then
[0, 1, 0, 2, 1, 1, 0, 0, 3, 3, 2]
else
[0, 1, 0, 2, 1, 3, 2, 2, 3, 0, 0])
else
(if i.val < 6327 then
[0, 1, 0, 2, 2, 3, 0, 1, 2, 2, 1]
else
[0, 1, 0, 2, 2, 3, 2, 2, 1, 1, 3])))
else
(if i.val < 6332 then
(if i.val < 6330 then
(if i.val < 6329 then
[0, 1, 0, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 1, 0, 2, 3, 0, 1, 2, 3, 3, 2])
else
(if i.val < 6331 then
[0, 1, 0, 2, 3, 3, 0, 1, 2, 3, 0]
else
[0, 1, 0, 3, 0, 0, 1, 2, 1, 3, 0]))
else
(if i.val < 6334 then
(if i.val < 6333 then
[0, 1, 0, 3, 0, 0, 1, 3, 2, 2, 1]
else
[0, 1, 0, 3, 0, 0, 2, 1, 3, 0, 0])
else
(if i.val < 6335 then
[0, 1, 0, 3, 0, 0, 2, 2, 1, 0, 3]
else
[0, 1, 0, 3, 0, 1, 1, 2, 2, 3, 0]))))))
else
(if i.val < 6368 then
(if i.val < 6352 then
(if i.val < 6344 then
(if i.val < 6340 then
(if i.val < 6338 then
(if i.val < 6337 then
[0, 1, 0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[0, 1, 0, 3, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 6339 then
[0, 1, 0, 3, 0, 2, 2, 1, 1, 3, 3]
else
[0, 1, 0, 3, 2, 1, 1, 0, 0, 2, 1]))
else
(if i.val < 6342 then
(if i.val < 6341 then
[0, 1, 0, 3, 2, 2, 1, 0, 0, 3, 0]
else
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1])
else
(if i.val < 6343 then
[0, 1, 0, 3, 2, 2, 1, 3, 0, 2, 1]
else
[0, 1, 0, 3, 2, 2, 3, 0, 0, 1, 1])))
else
(if i.val < 6348 then
(if i.val < 6346 then
(if i.val < 6345 then
[0, 1, 1, 0, 0, 2, 2, 1, 3, 3, 2]
else
[0, 1, 1, 0, 0, 3, 2, 2, 1, 1, 3])
else
(if i.val < 6347 then
[0, 1, 1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[0, 1, 1, 0, 2, 1, 0, 3, 2, 2, 3]))
else
(if i.val < 6350 then
(if i.val < 6349 then
[0, 1, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
[0, 1, 1, 0, 2, 2, 1, 3, 2, 2, 1])
else
(if i.val < 6351 then
[0, 1, 1, 0, 2, 3, 3, 0, 0, 2, 3]
else
[0, 1, 1, 0, 3, 0, 0, 1, 3, 2, 1]))))
else
(if i.val < 6360 then
(if i.val < 6356 then
(if i.val < 6354 then
(if i.val < 6353 then
[0, 1, 1, 0, 3, 0, 1, 2, 1, 1, 3]
else
[0, 1, 1, 0, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 6355 then
[0, 1, 1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 1, 1, 0, 3, 3, 0, 2, 3, 3, 2]))
else
(if i.val < 6358 then
(if i.val < 6357 then
[0, 1, 1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 1, 1, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 6359 then
[0, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1]
else
[0, 1, 1, 2, 2, 1, 3, 0, 0, 2, 1])))
else
(if i.val < 6364 then
(if i.val < 6362 then
(if i.val < 6361 then
[0, 1, 1, 2, 3, 0, 0, 2, 3, 3, 2]
else
[0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 2])
else
(if i.val < 6363 then
[0, 1, 1, 3, 0, 0, 1, 2, 1, 1, 3]
else
[0, 1, 1, 3, 0, 1, 1, 2, 2, 3, 0]))
else
(if i.val < 6366 then
(if i.val < 6365 then
[0, 1, 1, 3, 0, 2, 2, 1, 0, 3, 2]
else
[0, 1, 1, 3, 3, 0, 1, 2, 3, 0, 0])
else
(if i.val < 6367 then
[0, 1, 2, 1, 0, 0, 1, 2, 3, 0, 0]
else
[0, 1, 2, 1, 0, 3, 0, 2, 1, 0, 3])))))
else
(if i.val < 6384 then
(if i.val < 6376 then
(if i.val < 6372 then
(if i.val < 6370 then
(if i.val < 6369 then
[0, 1, 2, 1, 1, 3, 0, 0, 2, 2, 1]
else
[0, 1, 2, 1, 1, 3, 3, 0, 0, 2, 1])
else
(if i.val < 6371 then
[0, 1, 2, 1, 3, 0, 0, 1, 2, 1, 3]
else
[0, 1, 2, 2, 1, 0, 3, 0, 1, 2, 1]))
else
(if i.val < 6374 then
(if i.val < 6373 then
[0, 1, 2, 2, 1, 0, 3, 2, 2, 1, 3]
else
[0, 1, 2, 3, 0, 1, 2, 1, 1, 0, 3])
else
(if i.val < 6375 then
[0, 1, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 1, 3, 3, 2, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 6380 then
(if i.val < 6378 then
(if i.val < 6377 then
[0, 1, 3, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 2, 1, 0, 0, 1, 3, 2, 2, 1, 3])
else
(if i.val < 6379 then
[0, 2, 1, 0, 3, 0, 1, 1, 0, 2, 1]
else
[0, 2, 1, 0, 3, 0, 2, 2, 1, 0, 3]))
else
(if i.val < 6382 then
(if i.val < 6381 then
[0, 2, 1, 0, 3, 3, 0, 2, 3, 3, 2]
else
[0, 2, 1, 1, 0, 0, 2, 1, 3, 3, 2])
else
(if i.val < 6383 then
[0, 2, 2, 1, 3, 0, 0, 3, 2, 2, 1]
else
[0, 2, 3, 0, 2, 1, 1, 2, 3, 0, 1]))))
else
(if i.val < 6392 then
(if i.val < 6388 then
(if i.val < 6386 then
(if i.val < 6385 then
[0, 3, 0, 0, 1, 2, 3, 0, 1, 2, 2]
else
[0, 3, 0, 1, 1, 0, 2, 2, 3, 3, 2])
else
(if i.val < 6387 then
[0, 3, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[1, 0, 0, 1, 2, 3, 3, 0, 0, 2, 3]))
else
(if i.val < 6390 then
(if i.val < 6389 then
[1, 0, 3, 2, 2, 1, 0, 3, 2, 1, 1]
else
[0, 0, 1, 0, 0, 1, 2, 1, 1, 2, 3, 2])
else
(if i.val < 6391 then
[0, 0, 1, 0, 0, 1, 2, 1, 3, 3, 2, 2]
else
[0, 0, 1, 0, 0, 1, 2, 2, 1, 3, 3, 2])))
else
(if i.val < 6396 then
(if i.val < 6394 then
(if i.val < 6393 then
[0, 0, 1, 0, 0, 1, 2, 2, 3, 3, 0, 0]
else
[0, 0, 1, 0, 0, 1, 2, 3, 3, 0, 1, 2])
else
(if i.val < 6395 then
[0, 0, 1, 0, 0, 1, 3, 0, 0, 2, 2, 1]
else
[0, 0, 1, 0, 0, 1, 3, 0, 0, 3, 2, 1]))
else
(if i.val < 6398 then
(if i.val < 6397 then
[0, 0, 1, 0, 0, 1, 3, 0, 2, 1, 0, 3]
else
[0, 0, 1, 0, 0, 1, 3, 3, 0, 1, 2, 1])
else
(if i.val < 6399 then
[0, 0, 1, 0, 0, 1, 3, 3, 0, 2, 3, 3]
else
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 0])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetWordsPart0050 : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 6440 then
(if i.val < 6420 then
(if i.val < 6410 then
(if i.val < 6405 then
(if i.val < 6402 then
(if i.val < 6401 then
[0, 0, 1, 0, 0, 2, 1, 1, 2, 3, 0, 1]
else
[0, 0, 1, 0, 0, 2, 3, 0, 0, 1, 3, 2])
else
(if i.val < 6403 then
[0, 0, 1, 0, 0, 2, 3, 0, 1, 2, 2, 1]
else
(if i.val < 6404 then
[0, 0, 1, 0, 0, 2, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 0, 0, 2, 3, 3, 0, 0, 2, 3])))
else
(if i.val < 6407 then
(if i.val < 6406 then
[0, 0, 1, 0, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 0, 0, 3, 0, 2, 1, 1, 0, 3])
else
(if i.val < 6408 then
[0, 0, 1, 0, 0, 3, 2, 2, 1, 0, 3, 2]
else
(if i.val < 6409 then
[0, 0, 1, 0, 0, 3, 2, 2, 1, 1, 3, 2]
else
[0, 0, 1, 0, 0, 3, 3, 0, 2, 1, 0, 3]))))
else
(if i.val < 6415 then
(if i.val < 6412 then
(if i.val < 6411 then
[0, 0, 1, 0, 0, 3, 3, 0, 2, 3, 3, 2]
else
[0, 0, 1, 0, 2, 1, 1, 0, 0, 3, 0, 0])
else
(if i.val < 6413 then
[0, 0, 1, 0, 2, 1, 1, 0, 0, 3, 0, 1]
else
(if i.val < 6414 then
[0, 0, 1, 0, 2, 1, 1, 0, 0, 3, 3, 2]
else
[0, 0, 1, 0, 2, 1, 3, 2, 2, 3, 0, 0])))
else
(if i.val < 6417 then
(if i.val < 6416 then
[0, 0, 1, 0, 2, 2, 3, 0, 1, 2, 2, 1]
else
[0, 0, 1, 0, 2, 2, 3, 2, 2, 1, 1, 3])
else
(if i.val < 6418 then
[0, 0, 1, 0, 2, 3, 0, 0, 2, 3, 3, 2]
else
(if i.val < 6419 then
[0, 0, 1, 0, 2, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 0, 2, 3, 3, 0, 1, 2, 3, 0])))))
else
(if i.val < 6430 then
(if i.val < 6425 then
(if i.val < 6422 then
(if i.val < 6421 then
[0, 0, 1, 0, 3, 0, 0, 1, 2, 1, 3, 0]
else
[0, 0, 1, 0, 3, 0, 0, 1, 3, 2, 2, 1])
else
(if i.val < 6423 then
[0, 0, 1, 0, 3, 0, 0, 2, 1, 3, 0, 0]
else
(if i.val < 6424 then
[0, 0, 1, 0, 3, 0, 0, 2, 2, 1, 0, 3]
else
[0, 0, 1, 0, 3, 0, 1, 1, 2, 2, 3, 0])))
else
(if i.val < 6427 then
(if i.val < 6426 then
[0, 0, 1, 0, 3, 0, 2, 1, 0, 3, 0, 0]
else
[0, 0, 1, 0, 3, 0, 2, 2, 1, 1, 3, 2])
else
(if i.val < 6428 then
[0, 0, 1, 0, 3, 0, 2, 2, 1, 1, 3, 3]
else
(if i.val < 6429 then
[0, 0, 1, 0, 3, 2, 1, 1, 0, 0, 2, 1]
else
[0, 0, 1, 0, 3, 2, 2, 1, 0, 0, 3, 0]))))
else
(if i.val < 6435 then
(if i.val < 6432 then
(if i.val < 6431 then
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1]
else
[0, 0, 1, 0, 3, 2, 2, 1, 3, 0, 2, 1])
else
(if i.val < 6433 then
[0, 0, 1, 0, 3, 2, 2, 3, 0, 0, 1, 1]
else
(if i.val < 6434 then
[0, 0, 1, 1, 0, 0, 2, 2, 1, 3, 3, 2]
else
[0, 0, 1, 1, 0, 0, 3, 2, 2, 1, 1, 3])))
else
(if i.val < 6437 then
(if i.val < 6436 then
[0, 0, 1, 1, 0, 0, 3, 3, 0, 1, 2, 1]
else
[0, 0, 1, 1, 0, 2, 1, 0, 3, 2, 2, 3])
else
(if i.val < 6438 then
[0, 0, 1, 1, 0, 2, 1, 1, 2, 3, 0, 0]
else
(if i.val < 6439 then
[0, 0, 1, 1, 0, 2, 2, 1, 3, 2, 2, 1]
else
[0, 0, 1, 1, 0, 2, 3, 3, 0, 0, 2, 3]))))))
else
(if i.val < 6460 then
(if i.val < 6450 then
(if i.val < 6445 then
(if i.val < 6442 then
(if i.val < 6441 then
[0, 0, 1, 1, 0, 3, 0, 0, 1, 3, 2, 1]
else
[0, 0, 1, 1, 0, 3, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6443 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 3, 0, 0]
else
(if i.val < 6444 then
[0, 0, 1, 1, 0, 3, 0, 1, 2, 3, 3, 2]
else
[0, 0, 1, 1, 0, 3, 3, 0, 2, 3, 3, 2])))
else
(if i.val < 6447 then
(if i.val < 6446 then
[0, 0, 1, 1, 2, 1, 3, 3, 2, 1, 0, 3]
else
[0, 0, 1, 1, 2, 2, 1, 0, 3, 2, 1, 1])
else
(if i.val < 6448 then
[0, 0, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1]
else
(if i.val < 6449 then
[0, 0, 1, 1, 2, 2, 1, 3, 0, 0, 2, 1]
else
[0, 0, 1, 1, 2, 3, 0, 0, 2, 3, 3, 2]))))
else
(if i.val < 6455 then
(if i.val < 6452 then
(if i.val < 6451 then
[0, 0, 1, 1, 2, 3, 3, 0, 1, 1, 2, 2]
else
[0, 0, 1, 1, 3, 0, 0, 1, 2, 1, 1, 3])
else
(if i.val < 6453 then
[0, 0, 1, 1, 3, 0, 1, 1, 2, 2, 3, 0]
else
(if i.val < 6454 then
[0, 0, 1, 1, 3, 0, 2, 2, 1, 0, 3, 2]
else
[0, 0, 1, 1, 3, 3, 0, 1, 2, 3, 0, 0])))
else
(if i.val < 6457 then
(if i.val < 6456 then
[0, 0, 1, 2, 1, 0, 0, 1, 2, 3, 0, 0]
else
[0, 0, 1, 2, 1, 0, 3, 0, 2, 1, 0, 3])
else
(if i.val < 6458 then
[0, 0, 1, 2, 1, 1, 3, 0, 0, 2, 2, 1]
else
(if i.val < 6459 then
[0, 0, 1, 2, 1, 1, 3, 3, 0, 0, 2, 1]
else
[0, 0, 1, 2, 1, 3, 0, 0, 1, 2, 1, 3])))))
else
(if i.val < 6470 then
(if i.val < 6465 then
(if i.val < 6462 then
(if i.val < 6461 then
[0, 0, 1, 2, 2, 1, 0, 3, 0, 1, 2, 1]
else
[0, 0, 1, 2, 2, 1, 0, 3, 2, 2, 1, 3])
else
(if i.val < 6463 then
[0, 0, 1, 2, 3, 0, 1, 2, 1, 1, 0, 3]
else
(if i.val < 6464 then
[0, 0, 1, 3, 2, 2, 1, 0, 0, 1, 2, 3]
else
[0, 0, 1, 3, 3, 2, 1, 0, 3, 2, 1, 1])))
else
(if i.val < 6467 then
(if i.val < 6466 then
[0, 0, 1, 3, 3, 2, 1, 0, 3, 2, 2, 3]
else
[0, 0, 2, 1, 0, 0, 1, 3, 2, 2, 1, 3])
else
(if i.val < 6468 then
[0, 0, 2, 1, 0, 3, 0, 1, 1, 0, 2, 1]
else
(if i.val < 6469 then
[0, 0, 2, 1, 0, 3, 0, 2, 2, 1, 0, 3]
else
[0, 0, 2, 1, 0, 3, 3, 0, 2, 3, 3, 2]))))
else
(if i.val < 6475 then
(if i.val < 6472 then
(if i.val < 6471 then
[0, 0, 2, 1, 1, 0, 0, 2, 1, 3, 3, 2]
else
[0, 0, 2, 2, 1, 3, 0, 0, 3, 2, 2, 1])
else
(if i.val < 6473 then
[0, 0, 2, 3, 0, 2, 1, 1, 2, 3, 0, 1]
else
(if i.val < 6474 then
[0, 0, 3, 0, 0, 1, 2, 3, 0, 1, 2, 2]
else
[0, 0, 3, 0, 1, 1, 0, 2, 2, 3, 3, 2])))
else
(if i.val < 6477 then
(if i.val < 6476 then
[0, 0, 3, 2, 1, 0, 3, 2, 2, 1, 1, 3]
else
[0, 1, 0, 0, 1, 2, 3, 3, 0, 0, 2, 3])
else
(if i.val < 6478 then
[0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1, 1]
else
(if i.val < 6479 then
[0, 0, 1, 0, 0, 1, 2, 3, 3, 0, 0, 2, 3]
else
[0, 0, 1, 0, 3, 2, 2, 1, 0, 3, 2, 1, 1])))))))

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row13_cosetRepresentatives : Fin 6480 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 3200 then
(if i.val < 1536 then
(if i.val < 768 then
(if i.val < 384 then
(if i.val < 128 then
g32p_row13_cosetRepresentativesPart0000 i
else
(if i.val < 256 then
g32p_row13_cosetRepresentativesPart0001 i
else
g32p_row13_cosetRepresentativesPart0002 i))
else
(if i.val < 512 then
g32p_row13_cosetRepresentativesPart0003 i
else
(if i.val < 640 then
g32p_row13_cosetRepresentativesPart0004 i
else
g32p_row13_cosetRepresentativesPart0005 i)))
else
(if i.val < 1152 then
(if i.val < 896 then
g32p_row13_cosetRepresentativesPart0006 i
else
(if i.val < 1024 then
g32p_row13_cosetRepresentativesPart0007 i
else
g32p_row13_cosetRepresentativesPart0008 i))
else
(if i.val < 1280 then
g32p_row13_cosetRepresentativesPart0009 i
else
(if i.val < 1408 then
g32p_row13_cosetRepresentativesPart0010 i
else
g32p_row13_cosetRepresentativesPart0011 i))))
else
(if i.val < 2304 then
(if i.val < 1920 then
(if i.val < 1664 then
g32p_row13_cosetRepresentativesPart0012 i
else
(if i.val < 1792 then
g32p_row13_cosetRepresentativesPart0013 i
else
g32p_row13_cosetRepresentativesPart0014 i))
else
(if i.val < 2048 then
g32p_row13_cosetRepresentativesPart0015 i
else
(if i.val < 2176 then
g32p_row13_cosetRepresentativesPart0016 i
else
g32p_row13_cosetRepresentativesPart0017 i)))
else
(if i.val < 2688 then
(if i.val < 2432 then
g32p_row13_cosetRepresentativesPart0018 i
else
(if i.val < 2560 then
g32p_row13_cosetRepresentativesPart0019 i
else
g32p_row13_cosetRepresentativesPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row13_cosetRepresentativesPart0021 i
else
g32p_row13_cosetRepresentativesPart0022 i)
else
(if i.val < 3072 then
g32p_row13_cosetRepresentativesPart0023 i
else
g32p_row13_cosetRepresentativesPart0024 i)))))
else
(if i.val < 4864 then
(if i.val < 3968 then
(if i.val < 3584 then
(if i.val < 3328 then
g32p_row13_cosetRepresentativesPart0025 i
else
(if i.val < 3456 then
g32p_row13_cosetRepresentativesPart0026 i
else
g32p_row13_cosetRepresentativesPart0027 i))
else
(if i.val < 3712 then
g32p_row13_cosetRepresentativesPart0028 i
else
(if i.val < 3840 then
g32p_row13_cosetRepresentativesPart0029 i
else
g32p_row13_cosetRepresentativesPart0030 i)))
else
(if i.val < 4352 then
(if i.val < 4096 then
g32p_row13_cosetRepresentativesPart0031 i
else
(if i.val < 4224 then
g32p_row13_cosetRepresentativesPart0032 i
else
g32p_row13_cosetRepresentativesPart0033 i))
else
(if i.val < 4608 then
(if i.val < 4480 then
g32p_row13_cosetRepresentativesPart0034 i
else
g32p_row13_cosetRepresentativesPart0035 i)
else
(if i.val < 4736 then
g32p_row13_cosetRepresentativesPart0036 i
else
g32p_row13_cosetRepresentativesPart0037 i))))
else
(if i.val < 5632 then
(if i.val < 5248 then
(if i.val < 4992 then
g32p_row13_cosetRepresentativesPart0038 i
else
(if i.val < 5120 then
g32p_row13_cosetRepresentativesPart0039 i
else
g32p_row13_cosetRepresentativesPart0040 i))
else
(if i.val < 5376 then
g32p_row13_cosetRepresentativesPart0041 i
else
(if i.val < 5504 then
g32p_row13_cosetRepresentativesPart0042 i
else
g32p_row13_cosetRepresentativesPart0043 i)))
else
(if i.val < 6016 then
(if i.val < 5760 then
g32p_row13_cosetRepresentativesPart0044 i
else
(if i.val < 5888 then
g32p_row13_cosetRepresentativesPart0045 i
else
g32p_row13_cosetRepresentativesPart0046 i))
else
(if i.val < 6272 then
(if i.val < 6144 then
g32p_row13_cosetRepresentativesPart0047 i
else
g32p_row13_cosetRepresentativesPart0048 i)
else
(if i.val < 6400 then
g32p_row13_cosetRepresentativesPart0049 i
else
g32p_row13_cosetRepresentativesPart0050 i))))))

def g32p_row13_cosetWords : Fin 6480 → List (Fin 4) :=
  fun i => (if i.val < 3200 then
(if i.val < 1536 then
(if i.val < 768 then
(if i.val < 384 then
(if i.val < 128 then
g32p_row13_cosetWordsPart0000 i
else
(if i.val < 256 then
g32p_row13_cosetWordsPart0001 i
else
g32p_row13_cosetWordsPart0002 i))
else
(if i.val < 512 then
g32p_row13_cosetWordsPart0003 i
else
(if i.val < 640 then
g32p_row13_cosetWordsPart0004 i
else
g32p_row13_cosetWordsPart0005 i)))
else
(if i.val < 1152 then
(if i.val < 896 then
g32p_row13_cosetWordsPart0006 i
else
(if i.val < 1024 then
g32p_row13_cosetWordsPart0007 i
else
g32p_row13_cosetWordsPart0008 i))
else
(if i.val < 1280 then
g32p_row13_cosetWordsPart0009 i
else
(if i.val < 1408 then
g32p_row13_cosetWordsPart0010 i
else
g32p_row13_cosetWordsPart0011 i))))
else
(if i.val < 2304 then
(if i.val < 1920 then
(if i.val < 1664 then
g32p_row13_cosetWordsPart0012 i
else
(if i.val < 1792 then
g32p_row13_cosetWordsPart0013 i
else
g32p_row13_cosetWordsPart0014 i))
else
(if i.val < 2048 then
g32p_row13_cosetWordsPart0015 i
else
(if i.val < 2176 then
g32p_row13_cosetWordsPart0016 i
else
g32p_row13_cosetWordsPart0017 i)))
else
(if i.val < 2688 then
(if i.val < 2432 then
g32p_row13_cosetWordsPart0018 i
else
(if i.val < 2560 then
g32p_row13_cosetWordsPart0019 i
else
g32p_row13_cosetWordsPart0020 i))
else
(if i.val < 2944 then
(if i.val < 2816 then
g32p_row13_cosetWordsPart0021 i
else
g32p_row13_cosetWordsPart0022 i)
else
(if i.val < 3072 then
g32p_row13_cosetWordsPart0023 i
else
g32p_row13_cosetWordsPart0024 i)))))
else
(if i.val < 4864 then
(if i.val < 3968 then
(if i.val < 3584 then
(if i.val < 3328 then
g32p_row13_cosetWordsPart0025 i
else
(if i.val < 3456 then
g32p_row13_cosetWordsPart0026 i
else
g32p_row13_cosetWordsPart0027 i))
else
(if i.val < 3712 then
g32p_row13_cosetWordsPart0028 i
else
(if i.val < 3840 then
g32p_row13_cosetWordsPart0029 i
else
g32p_row13_cosetWordsPart0030 i)))
else
(if i.val < 4352 then
(if i.val < 4096 then
g32p_row13_cosetWordsPart0031 i
else
(if i.val < 4224 then
g32p_row13_cosetWordsPart0032 i
else
g32p_row13_cosetWordsPart0033 i))
else
(if i.val < 4608 then
(if i.val < 4480 then
g32p_row13_cosetWordsPart0034 i
else
g32p_row13_cosetWordsPart0035 i)
else
(if i.val < 4736 then
g32p_row13_cosetWordsPart0036 i
else
g32p_row13_cosetWordsPart0037 i))))
else
(if i.val < 5632 then
(if i.val < 5248 then
(if i.val < 4992 then
g32p_row13_cosetWordsPart0038 i
else
(if i.val < 5120 then
g32p_row13_cosetWordsPart0039 i
else
g32p_row13_cosetWordsPart0040 i))
else
(if i.val < 5376 then
g32p_row13_cosetWordsPart0041 i
else
(if i.val < 5504 then
g32p_row13_cosetWordsPart0042 i
else
g32p_row13_cosetWordsPart0043 i)))
else
(if i.val < 6016 then
(if i.val < 5760 then
g32p_row13_cosetWordsPart0044 i
else
(if i.val < 5888 then
g32p_row13_cosetWordsPart0045 i
else
g32p_row13_cosetWordsPart0046 i))
else
(if i.val < 6272 then
(if i.val < 6144 then
g32p_row13_cosetWordsPart0047 i
else
g32p_row13_cosetWordsPart0048 i)
else
(if i.val < 6400 then
g32p_row13_cosetWordsPart0049 i
else
g32p_row13_cosetWordsPart0050 i))))))

def g32p_row13_cosetGeneratorNextColumn0 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorNextColumn0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorNextColumn0Part0001 i
else
g32p_row13_cosetGeneratorNextColumn0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorNextColumn0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorNextColumn0Part0004 i
else
g32p_row13_cosetGeneratorNextColumn0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorNextColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorNextColumn0Part0007 i
else
g32p_row13_cosetGeneratorNextColumn0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorNextColumn0Part0009 i
else
g32p_row13_cosetGeneratorNextColumn0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorNextColumn0Part0011 i
else
g32p_row13_cosetGeneratorNextColumn0Part0012 i))))

def g32p_row13_cosetGeneratorNextColumn1 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorNextColumn1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorNextColumn1Part0001 i
else
g32p_row13_cosetGeneratorNextColumn1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorNextColumn1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorNextColumn1Part0004 i
else
g32p_row13_cosetGeneratorNextColumn1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorNextColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorNextColumn1Part0007 i
else
g32p_row13_cosetGeneratorNextColumn1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorNextColumn1Part0009 i
else
g32p_row13_cosetGeneratorNextColumn1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorNextColumn1Part0011 i
else
g32p_row13_cosetGeneratorNextColumn1Part0012 i))))

def g32p_row13_cosetGeneratorNextColumn2 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorNextColumn2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorNextColumn2Part0001 i
else
g32p_row13_cosetGeneratorNextColumn2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorNextColumn2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorNextColumn2Part0004 i
else
g32p_row13_cosetGeneratorNextColumn2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorNextColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorNextColumn2Part0007 i
else
g32p_row13_cosetGeneratorNextColumn2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorNextColumn2Part0009 i
else
g32p_row13_cosetGeneratorNextColumn2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorNextColumn2Part0011 i
else
g32p_row13_cosetGeneratorNextColumn2Part0012 i))))

def g32p_row13_cosetGeneratorNextColumn3 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorNextColumn3Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorNextColumn3Part0001 i
else
g32p_row13_cosetGeneratorNextColumn3Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorNextColumn3Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorNextColumn3Part0004 i
else
g32p_row13_cosetGeneratorNextColumn3Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorNextColumn3Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorNextColumn3Part0007 i
else
g32p_row13_cosetGeneratorNextColumn3Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorNextColumn3Part0009 i
else
g32p_row13_cosetGeneratorNextColumn3Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorNextColumn3Part0011 i
else
g32p_row13_cosetGeneratorNextColumn3Part0012 i))))

def g32p_row13_cosetGeneratorNext : Fin 4 → Fin 6480 → Fin 6480 :=
  ![g32p_row13_cosetGeneratorNextColumn0, g32p_row13_cosetGeneratorNextColumn1, g32p_row13_cosetGeneratorNextColumn2, g32p_row13_cosetGeneratorNextColumn3]

def g32p_row13_cosetGeneratorFactorColumn0 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorFactorColumn0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorFactorColumn0Part0001 i
else
g32p_row13_cosetGeneratorFactorColumn0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorFactorColumn0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorFactorColumn0Part0004 i
else
g32p_row13_cosetGeneratorFactorColumn0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorFactorColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorFactorColumn0Part0007 i
else
g32p_row13_cosetGeneratorFactorColumn0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorFactorColumn0Part0009 i
else
g32p_row13_cosetGeneratorFactorColumn0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorFactorColumn0Part0011 i
else
g32p_row13_cosetGeneratorFactorColumn0Part0012 i))))

def g32p_row13_cosetGeneratorFactorColumn1 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorFactorColumn1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorFactorColumn1Part0001 i
else
g32p_row13_cosetGeneratorFactorColumn1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorFactorColumn1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorFactorColumn1Part0004 i
else
g32p_row13_cosetGeneratorFactorColumn1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorFactorColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorFactorColumn1Part0007 i
else
g32p_row13_cosetGeneratorFactorColumn1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorFactorColumn1Part0009 i
else
g32p_row13_cosetGeneratorFactorColumn1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorFactorColumn1Part0011 i
else
g32p_row13_cosetGeneratorFactorColumn1Part0012 i))))

def g32p_row13_cosetGeneratorFactorColumn2 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorFactorColumn2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorFactorColumn2Part0001 i
else
g32p_row13_cosetGeneratorFactorColumn2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorFactorColumn2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorFactorColumn2Part0004 i
else
g32p_row13_cosetGeneratorFactorColumn2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorFactorColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorFactorColumn2Part0007 i
else
g32p_row13_cosetGeneratorFactorColumn2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorFactorColumn2Part0009 i
else
g32p_row13_cosetGeneratorFactorColumn2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorFactorColumn2Part0011 i
else
g32p_row13_cosetGeneratorFactorColumn2Part0012 i))))

def g32p_row13_cosetGeneratorFactorColumn3 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetGeneratorFactorColumn3Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetGeneratorFactorColumn3Part0001 i
else
g32p_row13_cosetGeneratorFactorColumn3Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetGeneratorFactorColumn3Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetGeneratorFactorColumn3Part0004 i
else
g32p_row13_cosetGeneratorFactorColumn3Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetGeneratorFactorColumn3Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetGeneratorFactorColumn3Part0007 i
else
g32p_row13_cosetGeneratorFactorColumn3Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetGeneratorFactorColumn3Part0009 i
else
g32p_row13_cosetGeneratorFactorColumn3Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetGeneratorFactorColumn3Part0011 i
else
g32p_row13_cosetGeneratorFactorColumn3Part0012 i))))

def g32p_row13_cosetGeneratorFactor : Fin 4 → Fin 6480 → Fin 24 :=
  ![g32p_row13_cosetGeneratorFactorColumn0, g32p_row13_cosetGeneratorFactorColumn1, g32p_row13_cosetGeneratorFactorColumn2, g32p_row13_cosetGeneratorFactorColumn3]

def g32p_row13_cosetBranchNextColumn0 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchNextColumn0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchNextColumn0Part0001 i
else
g32p_row13_cosetBranchNextColumn0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchNextColumn0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchNextColumn0Part0004 i
else
g32p_row13_cosetBranchNextColumn0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchNextColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchNextColumn0Part0007 i
else
g32p_row13_cosetBranchNextColumn0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchNextColumn0Part0009 i
else
g32p_row13_cosetBranchNextColumn0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchNextColumn0Part0011 i
else
g32p_row13_cosetBranchNextColumn0Part0012 i))))

def g32p_row13_cosetBranchNextColumn1 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchNextColumn1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchNextColumn1Part0001 i
else
g32p_row13_cosetBranchNextColumn1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchNextColumn1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchNextColumn1Part0004 i
else
g32p_row13_cosetBranchNextColumn1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchNextColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchNextColumn1Part0007 i
else
g32p_row13_cosetBranchNextColumn1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchNextColumn1Part0009 i
else
g32p_row13_cosetBranchNextColumn1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchNextColumn1Part0011 i
else
g32p_row13_cosetBranchNextColumn1Part0012 i))))

def g32p_row13_cosetBranchNextColumn2 : Fin 6480 → Fin 6480 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchNextColumn2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchNextColumn2Part0001 i
else
g32p_row13_cosetBranchNextColumn2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchNextColumn2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchNextColumn2Part0004 i
else
g32p_row13_cosetBranchNextColumn2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchNextColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchNextColumn2Part0007 i
else
g32p_row13_cosetBranchNextColumn2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchNextColumn2Part0009 i
else
g32p_row13_cosetBranchNextColumn2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchNextColumn2Part0011 i
else
g32p_row13_cosetBranchNextColumn2Part0012 i))))

def g32p_row13_cosetBranchNext : Fin 3 → Fin 6480 → Fin 6480 :=
  ![g32p_row13_cosetBranchNextColumn0, g32p_row13_cosetBranchNextColumn1, g32p_row13_cosetBranchNextColumn2]

def g32p_row13_cosetBranchFactorColumn0 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchFactorColumn0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchFactorColumn0Part0001 i
else
g32p_row13_cosetBranchFactorColumn0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchFactorColumn0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchFactorColumn0Part0004 i
else
g32p_row13_cosetBranchFactorColumn0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchFactorColumn0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchFactorColumn0Part0007 i
else
g32p_row13_cosetBranchFactorColumn0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchFactorColumn0Part0009 i
else
g32p_row13_cosetBranchFactorColumn0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchFactorColumn0Part0011 i
else
g32p_row13_cosetBranchFactorColumn0Part0012 i))))

def g32p_row13_cosetBranchFactorColumn1 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchFactorColumn1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchFactorColumn1Part0001 i
else
g32p_row13_cosetBranchFactorColumn1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchFactorColumn1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchFactorColumn1Part0004 i
else
g32p_row13_cosetBranchFactorColumn1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchFactorColumn1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchFactorColumn1Part0007 i
else
g32p_row13_cosetBranchFactorColumn1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchFactorColumn1Part0009 i
else
g32p_row13_cosetBranchFactorColumn1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchFactorColumn1Part0011 i
else
g32p_row13_cosetBranchFactorColumn1Part0012 i))))

def g32p_row13_cosetBranchFactorColumn2 : Fin 6480 → Fin 24 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetBranchFactorColumn2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetBranchFactorColumn2Part0001 i
else
g32p_row13_cosetBranchFactorColumn2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetBranchFactorColumn2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetBranchFactorColumn2Part0004 i
else
g32p_row13_cosetBranchFactorColumn2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetBranchFactorColumn2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetBranchFactorColumn2Part0007 i
else
g32p_row13_cosetBranchFactorColumn2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetBranchFactorColumn2Part0009 i
else
g32p_row13_cosetBranchFactorColumn2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetBranchFactorColumn2Part0011 i
else
g32p_row13_cosetBranchFactorColumn2Part0012 i))))

def g32p_row13_cosetBranchFactor : Fin 3 → Fin 6480 → Fin 24 :=
  ![g32p_row13_cosetBranchFactorColumn0, g32p_row13_cosetBranchFactorColumn1, g32p_row13_cosetBranchFactorColumn2]

def g32p_row13_cosetLabels0 : Fin 6480 → Fin 2160 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetLabels0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetLabels0Part0001 i
else
g32p_row13_cosetLabels0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetLabels0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetLabels0Part0004 i
else
g32p_row13_cosetLabels0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetLabels0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetLabels0Part0007 i
else
g32p_row13_cosetLabels0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetLabels0Part0009 i
else
g32p_row13_cosetLabels0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetLabels0Part0011 i
else
g32p_row13_cosetLabels0Part0012 i))))

def g32p_row13_cosetDistances0 : Fin 6480 → ℕ :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetDistances0Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetDistances0Part0001 i
else
g32p_row13_cosetDistances0Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetDistances0Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetDistances0Part0004 i
else
g32p_row13_cosetDistances0Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetDistances0Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetDistances0Part0007 i
else
g32p_row13_cosetDistances0Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetDistances0Part0009 i
else
g32p_row13_cosetDistances0Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetDistances0Part0011 i
else
g32p_row13_cosetDistances0Part0012 i))))

def g32p_row13_cosetRoots0 : Fin 2160 → Fin 6480 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetRoots0Part0000 i
else
g32p_row13_cosetRoots0Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetRoots0Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetRoots0Part0003 i
else
g32p_row13_cosetRoots0Part0004 i)))

def g32p_row13_cosetLengths0 : Fin 2160 → ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetLengths0Part0000 i
else
g32p_row13_cosetLengths0Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetLengths0Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetLengths0Part0003 i
else
g32p_row13_cosetLengths0Part0004 i)))

def g32p_row13_cosetCycleNodes0 : Fin 2160 → List ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetCycleNodes0Part0000 i
else
g32p_row13_cosetCycleNodes0Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetCycleNodes0Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetCycleNodes0Part0003 i
else
g32p_row13_cosetCycleNodes0Part0004 i)))

def g32p_row13_cosetCycles0 : List (List ℕ) :=
  List.ofFn g32p_row13_cosetCycleNodes0

def g32p_row13_cosetMonodromies0 : Fin 2160 → Fin 24 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetMonodromies0Part0000 i
else
g32p_row13_cosetMonodromies0Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetMonodromies0Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetMonodromies0Part0003 i
else
g32p_row13_cosetMonodromies0Part0004 i)))

def g32p_row13_cosetExponents0 : Fin 2160 → Multiplicative (ZMod 12) :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetExponents0Part0000 i
else
g32p_row13_cosetExponents0Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetExponents0Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetExponents0Part0003 i
else
g32p_row13_cosetExponents0Part0004 i)))

def g32p_row13_cosetLabels1 : Fin 6480 → Fin 2160 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetLabels1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetLabels1Part0001 i
else
g32p_row13_cosetLabels1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetLabels1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetLabels1Part0004 i
else
g32p_row13_cosetLabels1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetLabels1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetLabels1Part0007 i
else
g32p_row13_cosetLabels1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetLabels1Part0009 i
else
g32p_row13_cosetLabels1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetLabels1Part0011 i
else
g32p_row13_cosetLabels1Part0012 i))))

def g32p_row13_cosetDistances1 : Fin 6480 → ℕ :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetDistances1Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetDistances1Part0001 i
else
g32p_row13_cosetDistances1Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetDistances1Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetDistances1Part0004 i
else
g32p_row13_cosetDistances1Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetDistances1Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetDistances1Part0007 i
else
g32p_row13_cosetDistances1Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetDistances1Part0009 i
else
g32p_row13_cosetDistances1Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetDistances1Part0011 i
else
g32p_row13_cosetDistances1Part0012 i))))

def g32p_row13_cosetRoots1 : Fin 2160 → Fin 6480 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetRoots1Part0000 i
else
g32p_row13_cosetRoots1Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetRoots1Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetRoots1Part0003 i
else
g32p_row13_cosetRoots1Part0004 i)))

def g32p_row13_cosetLengths1 : Fin 2160 → ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetLengths1Part0000 i
else
g32p_row13_cosetLengths1Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetLengths1Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetLengths1Part0003 i
else
g32p_row13_cosetLengths1Part0004 i)))

def g32p_row13_cosetCycleNodes1 : Fin 2160 → List ℕ :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetCycleNodes1Part0000 i
else
g32p_row13_cosetCycleNodes1Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetCycleNodes1Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetCycleNodes1Part0003 i
else
g32p_row13_cosetCycleNodes1Part0004 i)))

def g32p_row13_cosetCycles1 : List (List ℕ) :=
  List.ofFn g32p_row13_cosetCycleNodes1

def g32p_row13_cosetMonodromies1 : Fin 2160 → Fin 24 :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetMonodromies1Part0000 i
else
g32p_row13_cosetMonodromies1Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetMonodromies1Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetMonodromies1Part0003 i
else
g32p_row13_cosetMonodromies1Part0004 i)))

def g32p_row13_cosetExponents1 : Fin 2160 → Multiplicative (ZMod 12) :=
  fun i => (if i.val < 1024 then
(if i.val < 512 then
g32p_row13_cosetExponents1Part0000 i
else
g32p_row13_cosetExponents1Part0001 i)
else
(if i.val < 1536 then
g32p_row13_cosetExponents1Part0002 i
else
(if i.val < 2048 then
g32p_row13_cosetExponents1Part0003 i
else
g32p_row13_cosetExponents1Part0004 i)))

def g32p_row13_cosetLabels2 : Fin 6480 → Fin 3312 :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetLabels2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetLabels2Part0001 i
else
g32p_row13_cosetLabels2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetLabels2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetLabels2Part0004 i
else
g32p_row13_cosetLabels2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetLabels2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetLabels2Part0007 i
else
g32p_row13_cosetLabels2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetLabels2Part0009 i
else
g32p_row13_cosetLabels2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetLabels2Part0011 i
else
g32p_row13_cosetLabels2Part0012 i))))

def g32p_row13_cosetDistances2 : Fin 6480 → ℕ :=
  fun i => (if i.val < 3072 then
(if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetDistances2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetDistances2Part0001 i
else
g32p_row13_cosetDistances2Part0002 i))
else
(if i.val < 2048 then
g32p_row13_cosetDistances2Part0003 i
else
(if i.val < 2560 then
g32p_row13_cosetDistances2Part0004 i
else
g32p_row13_cosetDistances2Part0005 i)))
else
(if i.val < 4608 then
(if i.val < 3584 then
g32p_row13_cosetDistances2Part0006 i
else
(if i.val < 4096 then
g32p_row13_cosetDistances2Part0007 i
else
g32p_row13_cosetDistances2Part0008 i))
else
(if i.val < 5632 then
(if i.val < 5120 then
g32p_row13_cosetDistances2Part0009 i
else
g32p_row13_cosetDistances2Part0010 i)
else
(if i.val < 6144 then
g32p_row13_cosetDistances2Part0011 i
else
g32p_row13_cosetDistances2Part0012 i))))

def g32p_row13_cosetRoots2 : Fin 3312 → Fin 6480 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetRoots2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetRoots2Part0001 i
else
g32p_row13_cosetRoots2Part0002 i))
else
(if i.val < 2560 then
(if i.val < 2048 then
g32p_row13_cosetRoots2Part0003 i
else
g32p_row13_cosetRoots2Part0004 i)
else
(if i.val < 3072 then
g32p_row13_cosetRoots2Part0005 i
else
g32p_row13_cosetRoots2Part0006 i)))

def g32p_row13_cosetLengths2 : Fin 3312 → ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetLengths2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetLengths2Part0001 i
else
g32p_row13_cosetLengths2Part0002 i))
else
(if i.val < 2560 then
(if i.val < 2048 then
g32p_row13_cosetLengths2Part0003 i
else
g32p_row13_cosetLengths2Part0004 i)
else
(if i.val < 3072 then
g32p_row13_cosetLengths2Part0005 i
else
g32p_row13_cosetLengths2Part0006 i)))

def g32p_row13_cosetCycleNodes2 : Fin 3312 → List ℕ :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetCycleNodes2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetCycleNodes2Part0001 i
else
g32p_row13_cosetCycleNodes2Part0002 i))
else
(if i.val < 2560 then
(if i.val < 2048 then
g32p_row13_cosetCycleNodes2Part0003 i
else
g32p_row13_cosetCycleNodes2Part0004 i)
else
(if i.val < 3072 then
g32p_row13_cosetCycleNodes2Part0005 i
else
g32p_row13_cosetCycleNodes2Part0006 i)))

def g32p_row13_cosetCycles2 : List (List ℕ) :=
  List.ofFn g32p_row13_cosetCycleNodes2

def g32p_row13_cosetMonodromies2 : Fin 3312 → Fin 24 :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetMonodromies2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetMonodromies2Part0001 i
else
g32p_row13_cosetMonodromies2Part0002 i))
else
(if i.val < 2560 then
(if i.val < 2048 then
g32p_row13_cosetMonodromies2Part0003 i
else
g32p_row13_cosetMonodromies2Part0004 i)
else
(if i.val < 3072 then
g32p_row13_cosetMonodromies2Part0005 i
else
g32p_row13_cosetMonodromies2Part0006 i)))

def g32p_row13_cosetExponents2 : Fin 3312 → Multiplicative (ZMod 12) :=
  fun i => (if i.val < 1536 then
(if i.val < 512 then
g32p_row13_cosetExponents2Part0000 i
else
(if i.val < 1024 then
g32p_row13_cosetExponents2Part0001 i
else
g32p_row13_cosetExponents2Part0002 i))
else
(if i.val < 2560 then
(if i.val < 2048 then
g32p_row13_cosetExponents2Part0003 i
else
g32p_row13_cosetExponents2Part0004 i)
else
(if i.val < 3072 then
g32p_row13_cosetExponents2Part0005 i
else
g32p_row13_cosetExponents2Part0006 i)))


end HodgeLean.Foundations.Program

end
