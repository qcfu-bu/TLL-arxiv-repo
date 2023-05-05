#include"runtime.h"

tll_ptr andb_i1(tll_ptr b1_v21784, tll_ptr b2_v21785);
tll_ptr orb_i2(tll_ptr b1_v21789, tll_ptr b2_v21790);
tll_ptr notb_i3(tll_ptr b_v21794);
tll_ptr lten_i4(tll_ptr x_v21796, tll_ptr y_v21797);
tll_ptr gten_i5(tll_ptr x_v21801, tll_ptr y_v21802);
tll_ptr ltn_i6(tll_ptr x_v21806, tll_ptr y_v21807);
tll_ptr gtn_i7(tll_ptr x_v21811, tll_ptr y_v21812);
tll_ptr eqn_i8(tll_ptr x_v21816, tll_ptr y_v21817);
tll_ptr pred_i9(tll_ptr x_v21821);
tll_ptr addn_i10(tll_ptr x_v21823, tll_ptr y_v21824);
tll_ptr subn_i11(tll_ptr x_v21828, tll_ptr y_v21829);
tll_ptr muln_i12(tll_ptr x_v21833, tll_ptr y_v21834);
tll_ptr divn_i13(tll_ptr x_v21838, tll_ptr y_v21839);
tll_ptr modn_i14(tll_ptr x_v21843, tll_ptr y_v21844);
tll_ptr cats_i15(tll_ptr s1_v21848, tll_ptr s2_v21849);
tll_ptr strlen_i16(tll_ptr s_v21855);
tll_ptr lenUU_i45(tll_ptr A_v21859, tll_ptr xs_v21860);
tll_ptr lenUL_i44(tll_ptr A_v21868, tll_ptr xs_v21869);
tll_ptr lenLL_i42(tll_ptr A_v21877, tll_ptr xs_v21878);
tll_ptr appendUU_i49(tll_ptr A_v21886, tll_ptr xs_v21887, tll_ptr ys_v21888);
tll_ptr appendUL_i48(tll_ptr A_v21897, tll_ptr xs_v21898, tll_ptr ys_v21899);
tll_ptr appendLL_i46(tll_ptr A_v21908, tll_ptr xs_v21909, tll_ptr ys_v21910);
tll_ptr readline_i25(tll_ptr __v21919);
tll_ptr print_i26(tll_ptr s_v21934);
tll_ptr prerr_i27(tll_ptr s_v21945);
tll_ptr get_at_i29(tll_ptr A_v21956, tll_ptr n_v21957, tll_ptr xs_v21958, tll_ptr a_v21959);
tll_ptr string_of_digit_i30(tll_ptr n_v21974);
tll_ptr string_of_nat_i31(tll_ptr n_v21976);
tll_ptr gcd_i32(tll_ptr a_v21980, tll_ptr b_v21981);
tll_ptr lcm_i33(tll_ptr a_v21985, tll_ptr b_v21986);
tll_ptr powm_i34(tll_ptr a_v21990, tll_ptr b_v21991, tll_ptr m_v21992);
tll_ptr server_i39(tll_ptr ch_v21999);
tll_ptr client_i40(tll_ptr ch_v22024);

tll_ptr addnclo_i59;
tll_ptr andbclo_i50;
tll_ptr appendLLclo_i71;
tll_ptr appendULclo_i70;
tll_ptr appendUUclo_i69;
tll_ptr catsclo_i64;
tll_ptr clientclo_i82;
tll_ptr digits_i28;
tll_ptr divnclo_i62;
tll_ptr eqnclo_i57;
tll_ptr gcdclo_i78;
tll_ptr get_atclo_i75;
tll_ptr gtenclo_i54;
tll_ptr gtnclo_i56;
tll_ptr lcmclo_i79;
tll_ptr lenLLclo_i68;
tll_ptr lenULclo_i67;
tll_ptr lenUUclo_i66;
tll_ptr ltenclo_i53;
tll_ptr ltnclo_i55;
tll_ptr modnclo_i63;
tll_ptr mulnclo_i61;
tll_ptr notbclo_i52;
tll_ptr orbclo_i51;
tll_ptr powmclo_i80;
tll_ptr predclo_i58;
tll_ptr prerrclo_i74;
tll_ptr printclo_i73;
tll_ptr readlineclo_i72;
tll_ptr serverclo_i81;
tll_ptr string_of_digitclo_i76;
tll_ptr string_of_natclo_i77;
tll_ptr strlenclo_i65;
tll_ptr subnclo_i60;

tll_ptr andb_i1(tll_ptr b1_v21784, tll_ptr b2_v21785) {
  tll_ptr ifte_ret_t1;
  if (b1_v21784) {
    ifte_ret_t1 = b2_v21785;
  }
  else {
    ifte_ret_t1 = (tll_ptr)0;
  }
  return ifte_ret_t1;
}

tll_ptr lam_fun_t3(tll_ptr b2_v21788, tll_env env) {
  tll_ptr call_ret_t2;
  call_ret_t2 = andb_i1(env[0], b2_v21788);
  return call_ret_t2;
}

tll_ptr lam_fun_t5(tll_ptr b1_v21786, tll_env env) {
  tll_ptr lam_clo_t4;
  instr_clo(&lam_clo_t4, &lam_fun_t3, 1, b1_v21786);
  return lam_clo_t4;
}

tll_ptr orb_i2(tll_ptr b1_v21789, tll_ptr b2_v21790) {
  tll_ptr ifte_ret_t7;
  if (b1_v21789) {
    ifte_ret_t7 = (tll_ptr)1;
  }
  else {
    ifte_ret_t7 = b2_v21790;
  }
  return ifte_ret_t7;
}

tll_ptr lam_fun_t9(tll_ptr b2_v21793, tll_env env) {
  tll_ptr call_ret_t8;
  call_ret_t8 = orb_i2(env[0], b2_v21793);
  return call_ret_t8;
}

tll_ptr lam_fun_t11(tll_ptr b1_v21791, tll_env env) {
  tll_ptr lam_clo_t10;
  instr_clo(&lam_clo_t10, &lam_fun_t9, 1, b1_v21791);
  return lam_clo_t10;
}

tll_ptr notb_i3(tll_ptr b_v21794) {
  tll_ptr ifte_ret_t13;
  if (b_v21794) {
    ifte_ret_t13 = (tll_ptr)0;
  }
  else {
    ifte_ret_t13 = (tll_ptr)1;
  }
  return ifte_ret_t13;
}

tll_ptr lam_fun_t15(tll_ptr b_v21795, tll_env env) {
  tll_ptr call_ret_t14;
  call_ret_t14 = notb_i3(b_v21795);
  return call_ret_t14;
}

tll_ptr lten_i4(tll_ptr x_v21796, tll_ptr y_v21797) {
  tll_ptr lten_ret_t17;
  instr_lten(&lten_ret_t17, x_v21796, y_v21797);
  return lten_ret_t17;
}

tll_ptr lam_fun_t19(tll_ptr y_v21800, tll_env env) {
  tll_ptr call_ret_t18;
  call_ret_t18 = lten_i4(env[0], y_v21800);
  return call_ret_t18;
}

tll_ptr lam_fun_t21(tll_ptr x_v21798, tll_env env) {
  tll_ptr lam_clo_t20;
  instr_clo(&lam_clo_t20, &lam_fun_t19, 1, x_v21798);
  return lam_clo_t20;
}

tll_ptr gten_i5(tll_ptr x_v21801, tll_ptr y_v21802) {
  tll_ptr gten_ret_t23;
  instr_gten(&gten_ret_t23, x_v21801, y_v21802);
  return gten_ret_t23;
}

tll_ptr lam_fun_t25(tll_ptr y_v21805, tll_env env) {
  tll_ptr call_ret_t24;
  call_ret_t24 = gten_i5(env[0], y_v21805);
  return call_ret_t24;
}

tll_ptr lam_fun_t27(tll_ptr x_v21803, tll_env env) {
  tll_ptr lam_clo_t26;
  instr_clo(&lam_clo_t26, &lam_fun_t25, 1, x_v21803);
  return lam_clo_t26;
}

tll_ptr ltn_i6(tll_ptr x_v21806, tll_ptr y_v21807) {
  tll_ptr ltn_ret_t29;
  instr_ltn(&ltn_ret_t29, x_v21806, y_v21807);
  return ltn_ret_t29;
}

tll_ptr lam_fun_t31(tll_ptr y_v21810, tll_env env) {
  tll_ptr call_ret_t30;
  call_ret_t30 = ltn_i6(env[0], y_v21810);
  return call_ret_t30;
}

tll_ptr lam_fun_t33(tll_ptr x_v21808, tll_env env) {
  tll_ptr lam_clo_t32;
  instr_clo(&lam_clo_t32, &lam_fun_t31, 1, x_v21808);
  return lam_clo_t32;
}

tll_ptr gtn_i7(tll_ptr x_v21811, tll_ptr y_v21812) {
  tll_ptr gtn_ret_t35;
  instr_gtn(&gtn_ret_t35, x_v21811, y_v21812);
  return gtn_ret_t35;
}

tll_ptr lam_fun_t37(tll_ptr y_v21815, tll_env env) {
  tll_ptr call_ret_t36;
  call_ret_t36 = gtn_i7(env[0], y_v21815);
  return call_ret_t36;
}

tll_ptr lam_fun_t39(tll_ptr x_v21813, tll_env env) {
  tll_ptr lam_clo_t38;
  instr_clo(&lam_clo_t38, &lam_fun_t37, 1, x_v21813);
  return lam_clo_t38;
}

tll_ptr eqn_i8(tll_ptr x_v21816, tll_ptr y_v21817) {
  tll_ptr eqn_ret_t41;
  instr_eqn(&eqn_ret_t41, x_v21816, y_v21817);
  return eqn_ret_t41;
}

tll_ptr lam_fun_t43(tll_ptr y_v21820, tll_env env) {
  tll_ptr call_ret_t42;
  call_ret_t42 = eqn_i8(env[0], y_v21820);
  return call_ret_t42;
}

tll_ptr lam_fun_t45(tll_ptr x_v21818, tll_env env) {
  tll_ptr lam_clo_t44;
  instr_clo(&lam_clo_t44, &lam_fun_t43, 1, x_v21818);
  return lam_clo_t44;
}

tll_ptr pred_i9(tll_ptr x_v21821) {
  tll_ptr add_ret_t47; tll_ptr ifte_ret_t48;
  if (x_v21821) {
    add_ret_t47 = x_v21821 - 1;
    ifte_ret_t48 = add_ret_t47;
  }
  else {
    ifte_ret_t48 = (tll_ptr)0;
  }
  return ifte_ret_t48;
}

tll_ptr lam_fun_t50(tll_ptr x_v21822, tll_env env) {
  tll_ptr call_ret_t49;
  call_ret_t49 = pred_i9(x_v21822);
  return call_ret_t49;
}

tll_ptr addn_i10(tll_ptr x_v21823, tll_ptr y_v21824) {
  tll_ptr addn_ret_t52;
  instr_addn(&addn_ret_t52, x_v21823, y_v21824);
  return addn_ret_t52;
}

tll_ptr lam_fun_t54(tll_ptr y_v21827, tll_env env) {
  tll_ptr call_ret_t53;
  call_ret_t53 = addn_i10(env[0], y_v21827);
  return call_ret_t53;
}

tll_ptr lam_fun_t56(tll_ptr x_v21825, tll_env env) {
  tll_ptr lam_clo_t55;
  instr_clo(&lam_clo_t55, &lam_fun_t54, 1, x_v21825);
  return lam_clo_t55;
}

tll_ptr subn_i11(tll_ptr x_v21828, tll_ptr y_v21829) {
  tll_ptr add_ret_t60; tll_ptr call_ret_t58; tll_ptr call_ret_t59;
  tll_ptr ifte_ret_t61;
  if (y_v21829) {
    call_ret_t59 = pred_i9(x_v21828);
    add_ret_t60 = y_v21829 - 1;
    call_ret_t58 = subn_i11(call_ret_t59, add_ret_t60);
    ifte_ret_t61 = call_ret_t58;
  }
  else {
    ifte_ret_t61 = x_v21828;
  }
  return ifte_ret_t61;
}

tll_ptr lam_fun_t63(tll_ptr y_v21832, tll_env env) {
  tll_ptr call_ret_t62;
  call_ret_t62 = subn_i11(env[0], y_v21832);
  return call_ret_t62;
}

tll_ptr lam_fun_t65(tll_ptr x_v21830, tll_env env) {
  tll_ptr lam_clo_t64;
  instr_clo(&lam_clo_t64, &lam_fun_t63, 1, x_v21830);
  return lam_clo_t64;
}

tll_ptr muln_i12(tll_ptr x_v21833, tll_ptr y_v21834) {
  tll_ptr muln_ret_t67;
  instr_muln(&muln_ret_t67, x_v21833, y_v21834);
  return muln_ret_t67;
}

tll_ptr lam_fun_t69(tll_ptr y_v21837, tll_env env) {
  tll_ptr call_ret_t68;
  call_ret_t68 = muln_i12(env[0], y_v21837);
  return call_ret_t68;
}

tll_ptr lam_fun_t71(tll_ptr x_v21835, tll_env env) {
  tll_ptr lam_clo_t70;
  instr_clo(&lam_clo_t70, &lam_fun_t69, 1, x_v21835);
  return lam_clo_t70;
}

tll_ptr divn_i13(tll_ptr x_v21838, tll_ptr y_v21839) {
  tll_ptr divn_ret_t73;
  instr_divn(&divn_ret_t73, x_v21838, y_v21839);
  return divn_ret_t73;
}

tll_ptr lam_fun_t75(tll_ptr y_v21842, tll_env env) {
  tll_ptr call_ret_t74;
  call_ret_t74 = divn_i13(env[0], y_v21842);
  return call_ret_t74;
}

tll_ptr lam_fun_t77(tll_ptr x_v21840, tll_env env) {
  tll_ptr lam_clo_t76;
  instr_clo(&lam_clo_t76, &lam_fun_t75, 1, x_v21840);
  return lam_clo_t76;
}

tll_ptr modn_i14(tll_ptr x_v21843, tll_ptr y_v21844) {
  tll_ptr modn_ret_t79;
  instr_modn(&modn_ret_t79, x_v21843, y_v21844);
  return modn_ret_t79;
}

tll_ptr lam_fun_t81(tll_ptr y_v21847, tll_env env) {
  tll_ptr call_ret_t80;
  call_ret_t80 = modn_i14(env[0], y_v21847);
  return call_ret_t80;
}

tll_ptr lam_fun_t83(tll_ptr x_v21845, tll_env env) {
  tll_ptr lam_clo_t82;
  instr_clo(&lam_clo_t82, &lam_fun_t81, 1, x_v21845);
  return lam_clo_t82;
}

tll_ptr cats_i15(tll_ptr s1_v21848, tll_ptr s2_v21849) {
  tll_ptr String_t87; tll_ptr c_v21850; tll_ptr call_ret_t86;
  tll_ptr s1_v21851; tll_ptr switch_ret_t85;
  switch(((tll_node)s1_v21848)->tag) {
    case 2:
      switch_ret_t85 = s2_v21849;
      break;
    case 3:
      c_v21850 = ((tll_node)s1_v21848)->data[0];
      s1_v21851 = ((tll_node)s1_v21848)->data[1];
      call_ret_t86 = cats_i15(s1_v21851, s2_v21849);
      instr_struct(&String_t87, 3, 2, c_v21850, call_ret_t86);
      switch_ret_t85 = String_t87;
      break;
  }
  return switch_ret_t85;
}

tll_ptr lam_fun_t89(tll_ptr s2_v21854, tll_env env) {
  tll_ptr call_ret_t88;
  call_ret_t88 = cats_i15(env[0], s2_v21854);
  return call_ret_t88;
}

tll_ptr lam_fun_t91(tll_ptr s1_v21852, tll_env env) {
  tll_ptr lam_clo_t90;
  instr_clo(&lam_clo_t90, &lam_fun_t89, 1, s1_v21852);
  return lam_clo_t90;
}

tll_ptr strlen_i16(tll_ptr s_v21855) {
  tll_ptr __v21856; tll_ptr add_ret_t95; tll_ptr call_ret_t94;
  tll_ptr s_v21857; tll_ptr switch_ret_t93;
  switch(((tll_node)s_v21855)->tag) {
    case 2:
      switch_ret_t93 = (tll_ptr)0;
      break;
    case 3:
      __v21856 = ((tll_node)s_v21855)->data[0];
      s_v21857 = ((tll_node)s_v21855)->data[1];
      call_ret_t94 = strlen_i16(s_v21857);
      add_ret_t95 = call_ret_t94 + 1;
      switch_ret_t93 = add_ret_t95;
      break;
  }
  return switch_ret_t93;
}

tll_ptr lam_fun_t97(tll_ptr s_v21858, tll_env env) {
  tll_ptr call_ret_t96;
  call_ret_t96 = strlen_i16(s_v21858);
  return call_ret_t96;
}

tll_ptr lenUU_i45(tll_ptr A_v21859, tll_ptr xs_v21860) {
  tll_ptr add_ret_t104; tll_ptr call_ret_t102; tll_ptr consUU_t105;
  tll_ptr n_v21863; tll_ptr nilUU_t100; tll_ptr pair_struct_t101;
  tll_ptr pair_struct_t106; tll_ptr switch_ret_t103; tll_ptr switch_ret_t99;
  tll_ptr x_v21861; tll_ptr xs_v21862; tll_ptr xs_v21864;
  switch(((tll_node)xs_v21860)->tag) {
    case 12:
      instr_struct(&nilUU_t100, 12, 0);
      instr_struct(&pair_struct_t101, 0, 2, (tll_ptr)0, nilUU_t100);
      switch_ret_t99 = pair_struct_t101;
      break;
    case 13:
      x_v21861 = ((tll_node)xs_v21860)->data[0];
      xs_v21862 = ((tll_node)xs_v21860)->data[1];
      call_ret_t102 = lenUU_i45(0, xs_v21862);
      switch(((tll_node)call_ret_t102)->tag) {
        case 0:
          n_v21863 = ((tll_node)call_ret_t102)->data[0];
          xs_v21864 = ((tll_node)call_ret_t102)->data[1];
          instr_free_struct(call_ret_t102);
          add_ret_t104 = n_v21863 + 1;
          instr_struct(&consUU_t105, 13, 2, x_v21861, xs_v21864);
          instr_struct(&pair_struct_t106, 0, 2, add_ret_t104, consUU_t105);
          switch_ret_t103 = pair_struct_t106;
          break;
      }
      switch_ret_t99 = switch_ret_t103;
      break;
  }
  return switch_ret_t99;
}

tll_ptr lam_fun_t108(tll_ptr xs_v21867, tll_env env) {
  tll_ptr call_ret_t107;
  call_ret_t107 = lenUU_i45(env[0], xs_v21867);
  return call_ret_t107;
}

tll_ptr lam_fun_t110(tll_ptr A_v21865, tll_env env) {
  tll_ptr lam_clo_t109;
  instr_clo(&lam_clo_t109, &lam_fun_t108, 1, A_v21865);
  return lam_clo_t109;
}

tll_ptr lenUL_i44(tll_ptr A_v21868, tll_ptr xs_v21869) {
  tll_ptr add_ret_t117; tll_ptr call_ret_t115; tll_ptr consUL_t118;
  tll_ptr n_v21872; tll_ptr nilUL_t113; tll_ptr pair_struct_t114;
  tll_ptr pair_struct_t119; tll_ptr switch_ret_t112; tll_ptr switch_ret_t116;
  tll_ptr x_v21870; tll_ptr xs_v21871; tll_ptr xs_v21873;
  switch(((tll_node)xs_v21869)->tag) {
    case 10:
      instr_free_struct(xs_v21869);
      instr_struct(&nilUL_t113, 10, 0);
      instr_struct(&pair_struct_t114, 0, 2, (tll_ptr)0, nilUL_t113);
      switch_ret_t112 = pair_struct_t114;
      break;
    case 11:
      x_v21870 = ((tll_node)xs_v21869)->data[0];
      xs_v21871 = ((tll_node)xs_v21869)->data[1];
      instr_free_struct(xs_v21869);
      call_ret_t115 = lenUL_i44(0, xs_v21871);
      switch(((tll_node)call_ret_t115)->tag) {
        case 0:
          n_v21872 = ((tll_node)call_ret_t115)->data[0];
          xs_v21873 = ((tll_node)call_ret_t115)->data[1];
          instr_free_struct(call_ret_t115);
          add_ret_t117 = n_v21872 + 1;
          instr_struct(&consUL_t118, 11, 2, x_v21870, xs_v21873);
          instr_struct(&pair_struct_t119, 0, 2, add_ret_t117, consUL_t118);
          switch_ret_t116 = pair_struct_t119;
          break;
      }
      switch_ret_t112 = switch_ret_t116;
      break;
  }
  return switch_ret_t112;
}

tll_ptr lam_fun_t121(tll_ptr xs_v21876, tll_env env) {
  tll_ptr call_ret_t120;
  call_ret_t120 = lenUL_i44(env[0], xs_v21876);
  return call_ret_t120;
}

tll_ptr lam_fun_t123(tll_ptr A_v21874, tll_env env) {
  tll_ptr lam_clo_t122;
  instr_clo(&lam_clo_t122, &lam_fun_t121, 1, A_v21874);
  return lam_clo_t122;
}

tll_ptr lenLL_i42(tll_ptr A_v21877, tll_ptr xs_v21878) {
  tll_ptr add_ret_t130; tll_ptr call_ret_t128; tll_ptr consLL_t131;
  tll_ptr n_v21881; tll_ptr nilLL_t126; tll_ptr pair_struct_t127;
  tll_ptr pair_struct_t132; tll_ptr switch_ret_t125; tll_ptr switch_ret_t129;
  tll_ptr x_v21879; tll_ptr xs_v21880; tll_ptr xs_v21882;
  switch(((tll_node)xs_v21878)->tag) {
    case 6:
      instr_free_struct(xs_v21878);
      instr_struct(&nilLL_t126, 6, 0);
      instr_struct(&pair_struct_t127, 0, 2, (tll_ptr)0, nilLL_t126);
      switch_ret_t125 = pair_struct_t127;
      break;
    case 7:
      x_v21879 = ((tll_node)xs_v21878)->data[0];
      xs_v21880 = ((tll_node)xs_v21878)->data[1];
      instr_free_struct(xs_v21878);
      call_ret_t128 = lenLL_i42(0, xs_v21880);
      switch(((tll_node)call_ret_t128)->tag) {
        case 0:
          n_v21881 = ((tll_node)call_ret_t128)->data[0];
          xs_v21882 = ((tll_node)call_ret_t128)->data[1];
          instr_free_struct(call_ret_t128);
          add_ret_t130 = n_v21881 + 1;
          instr_struct(&consLL_t131, 7, 2, x_v21879, xs_v21882);
          instr_struct(&pair_struct_t132, 0, 2, add_ret_t130, consLL_t131);
          switch_ret_t129 = pair_struct_t132;
          break;
      }
      switch_ret_t125 = switch_ret_t129;
      break;
  }
  return switch_ret_t125;
}

tll_ptr lam_fun_t134(tll_ptr xs_v21885, tll_env env) {
  tll_ptr call_ret_t133;
  call_ret_t133 = lenLL_i42(env[0], xs_v21885);
  return call_ret_t133;
}

tll_ptr lam_fun_t136(tll_ptr A_v21883, tll_env env) {
  tll_ptr lam_clo_t135;
  instr_clo(&lam_clo_t135, &lam_fun_t134, 1, A_v21883);
  return lam_clo_t135;
}

tll_ptr appendUU_i49(tll_ptr A_v21886, tll_ptr xs_v21887, tll_ptr ys_v21888) {
  tll_ptr call_ret_t139; tll_ptr consUU_t140; tll_ptr switch_ret_t138;
  tll_ptr x_v21889; tll_ptr xs_v21890;
  switch(((tll_node)xs_v21887)->tag) {
    case 12:
      switch_ret_t138 = ys_v21888;
      break;
    case 13:
      x_v21889 = ((tll_node)xs_v21887)->data[0];
      xs_v21890 = ((tll_node)xs_v21887)->data[1];
      call_ret_t139 = appendUU_i49(0, xs_v21890, ys_v21888);
      instr_struct(&consUU_t140, 13, 2, x_v21889, call_ret_t139);
      switch_ret_t138 = consUU_t140;
      break;
  }
  return switch_ret_t138;
}

tll_ptr lam_fun_t142(tll_ptr ys_v21896, tll_env env) {
  tll_ptr call_ret_t141;
  call_ret_t141 = appendUU_i49(env[1], env[0], ys_v21896);
  return call_ret_t141;
}

tll_ptr lam_fun_t144(tll_ptr xs_v21894, tll_env env) {
  tll_ptr lam_clo_t143;
  instr_clo(&lam_clo_t143, &lam_fun_t142, 2, xs_v21894, env[0]);
  return lam_clo_t143;
}

tll_ptr lam_fun_t146(tll_ptr A_v21891, tll_env env) {
  tll_ptr lam_clo_t145;
  instr_clo(&lam_clo_t145, &lam_fun_t144, 1, A_v21891);
  return lam_clo_t145;
}

tll_ptr appendUL_i48(tll_ptr A_v21897, tll_ptr xs_v21898, tll_ptr ys_v21899) {
  tll_ptr call_ret_t149; tll_ptr consUL_t150; tll_ptr switch_ret_t148;
  tll_ptr x_v21900; tll_ptr xs_v21901;
  switch(((tll_node)xs_v21898)->tag) {
    case 10:
      instr_free_struct(xs_v21898);
      switch_ret_t148 = ys_v21899;
      break;
    case 11:
      x_v21900 = ((tll_node)xs_v21898)->data[0];
      xs_v21901 = ((tll_node)xs_v21898)->data[1];
      instr_free_struct(xs_v21898);
      call_ret_t149 = appendUL_i48(0, xs_v21901, ys_v21899);
      instr_struct(&consUL_t150, 11, 2, x_v21900, call_ret_t149);
      switch_ret_t148 = consUL_t150;
      break;
  }
  return switch_ret_t148;
}

tll_ptr lam_fun_t152(tll_ptr ys_v21907, tll_env env) {
  tll_ptr call_ret_t151;
  call_ret_t151 = appendUL_i48(env[1], env[0], ys_v21907);
  return call_ret_t151;
}

tll_ptr lam_fun_t154(tll_ptr xs_v21905, tll_env env) {
  tll_ptr lam_clo_t153;
  instr_clo(&lam_clo_t153, &lam_fun_t152, 2, xs_v21905, env[0]);
  return lam_clo_t153;
}

tll_ptr lam_fun_t156(tll_ptr A_v21902, tll_env env) {
  tll_ptr lam_clo_t155;
  instr_clo(&lam_clo_t155, &lam_fun_t154, 1, A_v21902);
  return lam_clo_t155;
}

tll_ptr appendLL_i46(tll_ptr A_v21908, tll_ptr xs_v21909, tll_ptr ys_v21910) {
  tll_ptr call_ret_t159; tll_ptr consLL_t160; tll_ptr switch_ret_t158;
  tll_ptr x_v21911; tll_ptr xs_v21912;
  switch(((tll_node)xs_v21909)->tag) {
    case 6:
      instr_free_struct(xs_v21909);
      switch_ret_t158 = ys_v21910;
      break;
    case 7:
      x_v21911 = ((tll_node)xs_v21909)->data[0];
      xs_v21912 = ((tll_node)xs_v21909)->data[1];
      instr_free_struct(xs_v21909);
      call_ret_t159 = appendLL_i46(0, xs_v21912, ys_v21910);
      instr_struct(&consLL_t160, 7, 2, x_v21911, call_ret_t159);
      switch_ret_t158 = consLL_t160;
      break;
  }
  return switch_ret_t158;
}

tll_ptr lam_fun_t162(tll_ptr ys_v21918, tll_env env) {
  tll_ptr call_ret_t161;
  call_ret_t161 = appendLL_i46(env[1], env[0], ys_v21918);
  return call_ret_t161;
}

tll_ptr lam_fun_t164(tll_ptr xs_v21916, tll_env env) {
  tll_ptr lam_clo_t163;
  instr_clo(&lam_clo_t163, &lam_fun_t162, 2, xs_v21916, env[0]);
  return lam_clo_t163;
}

tll_ptr lam_fun_t166(tll_ptr A_v21913, tll_env env) {
  tll_ptr lam_clo_t165;
  instr_clo(&lam_clo_t165, &lam_fun_t164, 1, A_v21913);
  return lam_clo_t165;
}

tll_ptr lam_fun_t173(tll_ptr __v21920, tll_env env) {
  tll_ptr __v21929; tll_ptr ch_v21927; tll_ptr ch_v21928; tll_ptr ch_v21931;
  tll_ptr ch_v21932; tll_ptr prim_ch_t168; tll_ptr recv_msg_t170;
  tll_ptr s_v21930; tll_ptr send_ch_t169; tll_ptr send_ch_t172;
  tll_ptr switch_ret_t171;
  instr_open(&prim_ch_t168, &proc_stdin);
  ch_v21927 = prim_ch_t168;
  instr_send(&send_ch_t169, ch_v21927, (tll_ptr)1);
  ch_v21928 = send_ch_t169;
  instr_recv(&recv_msg_t170, ch_v21928);
  __v21929 = recv_msg_t170;
  switch(((tll_node)__v21929)->tag) {
    case 0:
      s_v21930 = ((tll_node)__v21929)->data[0];
      ch_v21931 = ((tll_node)__v21929)->data[1];
      instr_free_struct(__v21929);
      instr_send(&send_ch_t172, ch_v21931, (tll_ptr)0);
      ch_v21932 = send_ch_t172;
      switch_ret_t171 = s_v21930;
      break;
  }
  return switch_ret_t171;
}

tll_ptr readline_i25(tll_ptr __v21919) {
  tll_ptr lam_clo_t174;
  instr_clo(&lam_clo_t174, &lam_fun_t173, 0);
  return lam_clo_t174;
}

tll_ptr lam_fun_t176(tll_ptr __v21933, tll_env env) {
  tll_ptr call_ret_t175;
  call_ret_t175 = readline_i25(__v21933);
  return call_ret_t175;
}

tll_ptr lam_fun_t182(tll_ptr __v21935, tll_env env) {
  tll_ptr ch_v21940; tll_ptr ch_v21941; tll_ptr ch_v21942; tll_ptr ch_v21943;
  tll_ptr prim_ch_t178; tll_ptr send_ch_t179; tll_ptr send_ch_t180;
  tll_ptr send_ch_t181;
  instr_open(&prim_ch_t178, &proc_stdout);
  ch_v21940 = prim_ch_t178;
  instr_send(&send_ch_t179, ch_v21940, (tll_ptr)1);
  ch_v21941 = send_ch_t179;
  instr_send(&send_ch_t180, ch_v21941, env[0]);
  ch_v21942 = send_ch_t180;
  instr_send(&send_ch_t181, ch_v21942, (tll_ptr)0);
  ch_v21943 = send_ch_t181;
  return 0;
}

tll_ptr print_i26(tll_ptr s_v21934) {
  tll_ptr lam_clo_t183;
  instr_clo(&lam_clo_t183, &lam_fun_t182, 1, s_v21934);
  return lam_clo_t183;
}

tll_ptr lam_fun_t185(tll_ptr s_v21944, tll_env env) {
  tll_ptr call_ret_t184;
  call_ret_t184 = print_i26(s_v21944);
  return call_ret_t184;
}

tll_ptr lam_fun_t191(tll_ptr __v21946, tll_env env) {
  tll_ptr ch_v21951; tll_ptr ch_v21952; tll_ptr ch_v21953; tll_ptr ch_v21954;
  tll_ptr prim_ch_t187; tll_ptr send_ch_t188; tll_ptr send_ch_t189;
  tll_ptr send_ch_t190;
  instr_open(&prim_ch_t187, &proc_stderr);
  ch_v21951 = prim_ch_t187;
  instr_send(&send_ch_t188, ch_v21951, (tll_ptr)1);
  ch_v21952 = send_ch_t188;
  instr_send(&send_ch_t189, ch_v21952, env[0]);
  ch_v21953 = send_ch_t189;
  instr_send(&send_ch_t190, ch_v21953, (tll_ptr)0);
  ch_v21954 = send_ch_t190;
  return 0;
}

tll_ptr prerr_i27(tll_ptr s_v21945) {
  tll_ptr lam_clo_t192;
  instr_clo(&lam_clo_t192, &lam_fun_t191, 1, s_v21945);
  return lam_clo_t192;
}

tll_ptr lam_fun_t194(tll_ptr s_v21955, tll_env env) {
  tll_ptr call_ret_t193;
  call_ret_t193 = prerr_i27(s_v21955);
  return call_ret_t193;
}

tll_ptr get_at_i29(tll_ptr A_v21956, tll_ptr n_v21957, tll_ptr xs_v21958, tll_ptr a_v21959) {
  tll_ptr __v21960; tll_ptr __v21963; tll_ptr add_ret_t239;
  tll_ptr call_ret_t238; tll_ptr ifte_ret_t241; tll_ptr switch_ret_t237;
  tll_ptr switch_ret_t240; tll_ptr x_v21962; tll_ptr xs_v21961;
  if (n_v21957) {
    switch(((tll_node)xs_v21958)->tag) {
      case 12:
        switch_ret_t237 = a_v21959;
        break;
      case 13:
        __v21960 = ((tll_node)xs_v21958)->data[0];
        xs_v21961 = ((tll_node)xs_v21958)->data[1];
        add_ret_t239 = n_v21957 - 1;
        call_ret_t238 = get_at_i29(0, add_ret_t239, xs_v21961, a_v21959);
        switch_ret_t237 = call_ret_t238;
        break;
    }
    ifte_ret_t241 = switch_ret_t237;
  }
  else {
    switch(((tll_node)xs_v21958)->tag) {
      case 12:
        switch_ret_t240 = a_v21959;
        break;
      case 13:
        x_v21962 = ((tll_node)xs_v21958)->data[0];
        __v21963 = ((tll_node)xs_v21958)->data[1];
        switch_ret_t240 = x_v21962;
        break;
    }
    ifte_ret_t241 = switch_ret_t240;
  }
  return ifte_ret_t241;
}

tll_ptr lam_fun_t243(tll_ptr a_v21973, tll_env env) {
  tll_ptr call_ret_t242;
  call_ret_t242 = get_at_i29(env[2], env[1], env[0], a_v21973);
  return call_ret_t242;
}

tll_ptr lam_fun_t245(tll_ptr xs_v21971, tll_env env) {
  tll_ptr lam_clo_t244;
  instr_clo(&lam_clo_t244, &lam_fun_t243, 3, xs_v21971, env[0], env[1]);
  return lam_clo_t244;
}

tll_ptr lam_fun_t247(tll_ptr n_v21968, tll_env env) {
  tll_ptr lam_clo_t246;
  instr_clo(&lam_clo_t246, &lam_fun_t245, 2, n_v21968, env[0]);
  return lam_clo_t246;
}

tll_ptr lam_fun_t249(tll_ptr A_v21964, tll_env env) {
  tll_ptr lam_clo_t248;
  instr_clo(&lam_clo_t248, &lam_fun_t247, 1, A_v21964);
  return lam_clo_t248;
}

tll_ptr string_of_digit_i30(tll_ptr n_v21974) {
  tll_ptr EmptyString_t252; tll_ptr call_ret_t251;
  instr_struct(&EmptyString_t252, 2, 0);
  call_ret_t251 = get_at_i29(0, n_v21974, digits_i28, EmptyString_t252);
  return call_ret_t251;
}

tll_ptr lam_fun_t254(tll_ptr n_v21975, tll_env env) {
  tll_ptr call_ret_t253;
  call_ret_t253 = string_of_digit_i30(n_v21975);
  return call_ret_t253;
}

tll_ptr string_of_nat_i31(tll_ptr n_v21976) {
  tll_ptr call_ret_t256; tll_ptr call_ret_t257; tll_ptr call_ret_t258;
  tll_ptr call_ret_t259; tll_ptr call_ret_t260; tll_ptr call_ret_t261;
  tll_ptr ifte_ret_t262; tll_ptr n_v21978; tll_ptr s_v21977;
  call_ret_t257 = modn_i14(n_v21976, (tll_ptr)10);
  call_ret_t256 = string_of_digit_i30(call_ret_t257);
  s_v21977 = call_ret_t256;
  call_ret_t258 = divn_i13(n_v21976, (tll_ptr)10);
  n_v21978 = call_ret_t258;
  call_ret_t259 = ltn_i6((tll_ptr)0, n_v21978);
  if (call_ret_t259) {
    call_ret_t261 = string_of_nat_i31(n_v21978);
    call_ret_t260 = cats_i15(call_ret_t261, s_v21977);
    ifte_ret_t262 = call_ret_t260;
  }
  else {
    ifte_ret_t262 = s_v21977;
  }
  return ifte_ret_t262;
}

tll_ptr lam_fun_t264(tll_ptr n_v21979, tll_env env) {
  tll_ptr call_ret_t263;
  call_ret_t263 = string_of_nat_i31(n_v21979);
  return call_ret_t263;
}

tll_ptr gcd_i32(tll_ptr a_v21980, tll_ptr b_v21981) {
  tll_ptr call_ret_t266; tll_ptr call_ret_t267; tll_ptr ifte_ret_t268;
  if (b_v21981) {
    call_ret_t267 = modn_i14(a_v21980, b_v21981);
    call_ret_t266 = gcd_i32(b_v21981, call_ret_t267);
    ifte_ret_t268 = call_ret_t266;
  }
  else {
    ifte_ret_t268 = a_v21980;
  }
  return ifte_ret_t268;
}

tll_ptr lam_fun_t270(tll_ptr b_v21984, tll_env env) {
  tll_ptr call_ret_t269;
  call_ret_t269 = gcd_i32(env[0], b_v21984);
  return call_ret_t269;
}

tll_ptr lam_fun_t272(tll_ptr a_v21982, tll_env env) {
  tll_ptr lam_clo_t271;
  instr_clo(&lam_clo_t271, &lam_fun_t270, 1, a_v21982);
  return lam_clo_t271;
}

tll_ptr lcm_i33(tll_ptr a_v21985, tll_ptr b_v21986) {
  tll_ptr call_ret_t274; tll_ptr call_ret_t275; tll_ptr call_ret_t276;
  call_ret_t275 = muln_i12(a_v21985, b_v21986);
  call_ret_t276 = gcd_i32(a_v21985, b_v21986);
  call_ret_t274 = divn_i13(call_ret_t275, call_ret_t276);
  return call_ret_t274;
}

tll_ptr lam_fun_t278(tll_ptr b_v21989, tll_env env) {
  tll_ptr call_ret_t277;
  call_ret_t277 = lcm_i33(env[0], b_v21989);
  return call_ret_t277;
}

tll_ptr lam_fun_t280(tll_ptr a_v21987, tll_env env) {
  tll_ptr lam_clo_t279;
  instr_clo(&lam_clo_t279, &lam_fun_t278, 1, a_v21987);
  return lam_clo_t279;
}

tll_ptr powm_i34(tll_ptr a_v21990, tll_ptr b_v21991, tll_ptr m_v21992) {
  tll_ptr add_ret_t285; tll_ptr call_ret_t282; tll_ptr call_ret_t283;
  tll_ptr call_ret_t284; tll_ptr ifte_ret_t286;
  if (b_v21991) {
    add_ret_t285 = b_v21991 - 1;
    call_ret_t284 = powm_i34(a_v21990, add_ret_t285, m_v21992);
    call_ret_t283 = muln_i12(a_v21990, call_ret_t284);
    call_ret_t282 = modn_i14(call_ret_t283, m_v21992);
    ifte_ret_t286 = call_ret_t282;
  }
  else {
    ifte_ret_t286 = (tll_ptr)1;
  }
  return ifte_ret_t286;
}

tll_ptr lam_fun_t288(tll_ptr m_v21998, tll_env env) {
  tll_ptr call_ret_t287;
  call_ret_t287 = powm_i34(env[1], env[0], m_v21998);
  return call_ret_t287;
}

tll_ptr lam_fun_t290(tll_ptr b_v21996, tll_env env) {
  tll_ptr lam_clo_t289;
  instr_clo(&lam_clo_t289, &lam_fun_t288, 2, b_v21996, env[0]);
  return lam_clo_t289;
}

tll_ptr lam_fun_t292(tll_ptr a_v21993, tll_env env) {
  tll_ptr lam_clo_t291;
  instr_clo(&lam_clo_t291, &lam_fun_t290, 1, a_v21993);
  return lam_clo_t291;
}

tll_ptr lam_fun_t314(tll_ptr __v22002, tll_env env) {
  tll_ptr C_v22018; tll_ptr Char_t310; tll_ptr EmptyString_t311;
  tll_ptr P0_v22015; tll_ptr P1_v22022; tll_ptr String_t312;
  tll_ptr __v22017; tll_ptr app_ret_t313; tll_ptr call_ret_t306;
  tll_ptr call_ret_t307; tll_ptr call_ret_t308; tll_ptr call_ret_t309;
  tll_ptr ch_v22013; tll_ptr ch_v22014; tll_ptr ch_v22016; tll_ptr ch_v22019;
  tll_ptr ch_v22021; tll_ptr pair_struct_t300; tll_ptr pair_struct_t304;
  tll_ptr pf_v22020; tll_ptr recv_msg_t302; tll_ptr send_ch_t298;
  tll_ptr send_ch_t299; tll_ptr switch_ret_t301; tll_ptr switch_ret_t303;
  tll_ptr switch_ret_t305;
  instr_send(&send_ch_t298, env[1], env[0]);
  ch_v22013 = send_ch_t298;
  instr_send(&send_ch_t299, ch_v22013, (tll_ptr)17);
  ch_v22014 = send_ch_t299;
  instr_struct(&pair_struct_t300, 0, 2, 0, ch_v22014);
  switch(((tll_node)pair_struct_t300)->tag) {
    case 0:
      P0_v22015 = ((tll_node)pair_struct_t300)->data[0];
      ch_v22016 = ((tll_node)pair_struct_t300)->data[1];
      instr_free_struct(pair_struct_t300);
      instr_recv(&recv_msg_t302, ch_v22016);
      __v22017 = recv_msg_t302;
      switch(((tll_node)__v22017)->tag) {
        case 0:
          C_v22018 = ((tll_node)__v22017)->data[0];
          ch_v22019 = ((tll_node)__v22017)->data[1];
          instr_free_struct(__v22017);
          instr_struct(&pair_struct_t304, 0, 2, 0, ch_v22019);
          switch(((tll_node)pair_struct_t304)->tag) {
            case 0:
              pf_v22020 = ((tll_node)pair_struct_t304)->data[0];
              ch_v22021 = ((tll_node)pair_struct_t304)->data[1];
              instr_free_struct(pair_struct_t304);
              call_ret_t306 = powm_i34(C_v22018, (tll_ptr)413, env[0]);
              P1_v22022 = call_ret_t306;
              call_ret_t309 = string_of_nat_i31(P1_v22022);
              instr_struct(&Char_t310, 1, 1, (tll_ptr)10);
              instr_struct(&EmptyString_t311, 2, 0);
              instr_struct(&String_t312, 3, 2, Char_t310, EmptyString_t311);
              call_ret_t308 = cats_i15(call_ret_t309, String_t312);
              call_ret_t307 = print_i26(call_ret_t308);
              instr_app(&app_ret_t313, call_ret_t307, 0);
              instr_free_clo(call_ret_t307);
              switch_ret_t305 = app_ret_t313;
              break;
          }
          switch_ret_t303 = switch_ret_t305;
          break;
      }
      switch_ret_t301 = switch_ret_t303;
      break;
  }
  return switch_ret_t301;
}

tll_ptr server_i39(tll_ptr ch_v21999) {
  tll_ptr call_ret_t294; tll_ptr call_ret_t295; tll_ptr call_ret_t296;
  tll_ptr call_ret_t297; tll_ptr lam_clo_t315; tll_ptr n_v22000;
  tll_ptr tot_v22001;
  call_ret_t294 = muln_i12((tll_ptr)61, (tll_ptr)53);
  n_v22000 = call_ret_t294;
  call_ret_t296 = subn_i11((tll_ptr)61, (tll_ptr)1);
  call_ret_t297 = subn_i11((tll_ptr)53, (tll_ptr)1);
  call_ret_t295 = lcm_i33(call_ret_t296, call_ret_t297);
  tot_v22001 = call_ret_t295;
  instr_clo(&lam_clo_t315, &lam_fun_t314, 2, n_v22000, ch_v21999);
  return lam_clo_t315;
}

tll_ptr lam_fun_t317(tll_ptr ch_v22023, tll_env env) {
  tll_ptr call_ret_t316;
  call_ret_t316 = server_i39(ch_v22023);
  return call_ret_t316;
}

tll_ptr lam_fun_t342(tll_ptr __v22025, tll_env env) {
  tll_ptr __v22054; tll_ptr __v22063; tll_ptr call_ret_t339;
  tll_ptr ch_v22051; tll_ptr ch_v22053; tll_ptr ch_v22056; tll_ptr ch_v22058;
  tll_ptr ch_v22060; tll_ptr ch_v22062; tll_ptr ch_v22065; tll_ptr ch_v22067;
  tll_ptr ch_v22069; tll_ptr ch_v22071; tll_ptr ch_v22072;
  tll_ptr close_tmp_t341; tll_ptr e_v22064; tll_ptr n_v22055;
  tll_ptr pair_struct_t319; tll_ptr pair_struct_t321;
  tll_ptr pair_struct_t325; tll_ptr pair_struct_t327;
  tll_ptr pair_struct_t329; tll_ptr pair_struct_t333;
  tll_ptr pair_struct_t335; tll_ptr pair_struct_t337; tll_ptr pf1_v22057;
  tll_ptr pf2_v22061; tll_ptr pf3_v22066; tll_ptr pf4_v22068;
  tll_ptr pf5_v22070; tll_ptr recv_msg_t323; tll_ptr recv_msg_t331;
  tll_ptr send_ch_t340; tll_ptr switch_ret_t320; tll_ptr switch_ret_t322;
  tll_ptr switch_ret_t324; tll_ptr switch_ret_t326; tll_ptr switch_ret_t328;
  tll_ptr switch_ret_t330; tll_ptr switch_ret_t332; tll_ptr switch_ret_t334;
  tll_ptr switch_ret_t336; tll_ptr switch_ret_t338; tll_ptr tot_v22059;
  tll_ptr x_v22050; tll_ptr x_v22073; tll_ptr y_v22052;
  instr_struct(&pair_struct_t319, 0, 2, 0, env[0]);
  switch(((tll_node)pair_struct_t319)->tag) {
    case 0:
      x_v22050 = ((tll_node)pair_struct_t319)->data[0];
      ch_v22051 = ((tll_node)pair_struct_t319)->data[1];
      instr_free_struct(pair_struct_t319);
      instr_struct(&pair_struct_t321, 0, 2, 0, ch_v22051);
      switch(((tll_node)pair_struct_t321)->tag) {
        case 0:
          y_v22052 = ((tll_node)pair_struct_t321)->data[0];
          ch_v22053 = ((tll_node)pair_struct_t321)->data[1];
          instr_free_struct(pair_struct_t321);
          instr_recv(&recv_msg_t323, ch_v22053);
          __v22054 = recv_msg_t323;
          switch(((tll_node)__v22054)->tag) {
            case 0:
              n_v22055 = ((tll_node)__v22054)->data[0];
              ch_v22056 = ((tll_node)__v22054)->data[1];
              instr_free_struct(__v22054);
              instr_struct(&pair_struct_t325, 0, 2, 0, ch_v22056);
              switch(((tll_node)pair_struct_t325)->tag) {
                case 0:
                  pf1_v22057 = ((tll_node)pair_struct_t325)->data[0];
                  ch_v22058 = ((tll_node)pair_struct_t325)->data[1];
                  instr_free_struct(pair_struct_t325);
                  instr_struct(&pair_struct_t327, 0, 2, 0, ch_v22058);
                  switch(((tll_node)pair_struct_t327)->tag) {
                    case 0:
                      tot_v22059 = ((tll_node)pair_struct_t327)->data[0];
                      ch_v22060 = ((tll_node)pair_struct_t327)->data[1];
                      instr_free_struct(pair_struct_t327);
                      instr_struct(&pair_struct_t329, 0, 2, 0, ch_v22060);
                      switch(((tll_node)pair_struct_t329)->tag) {
                        case 0:
                          pf2_v22061 = ((tll_node)pair_struct_t329)->data[0];
                          ch_v22062 = ((tll_node)pair_struct_t329)->data[1];
                          instr_free_struct(pair_struct_t329);
                          instr_recv(&recv_msg_t331, ch_v22062);
                          __v22063 = recv_msg_t331;
                          switch(((tll_node)__v22063)->tag) {
                            case 0:
                              e_v22064 = ((tll_node)__v22063)->data[0];
                              ch_v22065 = ((tll_node)__v22063)->data[1];
                              instr_free_struct(__v22063);
                              instr_struct(&pair_struct_t333, 0, 2,
                                           0, ch_v22065);
                              switch(((tll_node)pair_struct_t333)->tag) {
                                case 0:
                                  pf3_v22066 = ((tll_node)pair_struct_t333)->data[0];
                                  ch_v22067 = ((tll_node)pair_struct_t333)->data[1];
                                  instr_free_struct(pair_struct_t333);
                                  instr_struct(&pair_struct_t335, 0, 2,
                                               0, ch_v22067);
                                  switch(((tll_node)pair_struct_t335)->tag) {
                                    case 0:
                                      pf4_v22068 = ((tll_node)pair_struct_t335)->data[0];
                                      ch_v22069 = ((tll_node)pair_struct_t335)->data[1];
                                      instr_free_struct(pair_struct_t335);
                                      instr_struct(&pair_struct_t337, 0, 2,
                                                   0, ch_v22069);
                                      switch(((tll_node)pair_struct_t337)->tag) {
                                        case 0:
                                          pf5_v22070 = ((tll_node)pair_struct_t337)->data[0];
                                          ch_v22071 = ((tll_node)pair_struct_t337)->data[1];
                                          instr_free_struct(pair_struct_t337);
                                          call_ret_t339 = powm_i34((tll_ptr)123,
                                                                   e_v22064,
                                                                   n_v22055);
                                          x_v22073 = call_ret_t339;
                                          instr_send(&send_ch_t340, ch_v22071, x_v22073);
                                          ch_v22072 = send_ch_t340;
                                          instr_close(&close_tmp_t341, ch_v22072);
                                          switch_ret_t338 = close_tmp_t341;
                                          break;
                                      }
                                      switch_ret_t336 = switch_ret_t338;
                                      break;
                                  }
                                  switch_ret_t334 = switch_ret_t336;
                                  break;
                              }
                              switch_ret_t332 = switch_ret_t334;
                              break;
                          }
                          switch_ret_t330 = switch_ret_t332;
                          break;
                      }
                      switch_ret_t328 = switch_ret_t330;
                      break;
                  }
                  switch_ret_t326 = switch_ret_t328;
                  break;
              }
              switch_ret_t324 = switch_ret_t326;
              break;
          }
          switch_ret_t322 = switch_ret_t324;
          break;
      }
      switch_ret_t320 = switch_ret_t322;
      break;
  }
  return switch_ret_t320;
}

tll_ptr client_i40(tll_ptr ch_v22024) {
  tll_ptr lam_clo_t343;
  instr_clo(&lam_clo_t343, &lam_fun_t342, 1, ch_v22024);
  return lam_clo_t343;
}

tll_ptr lam_fun_t345(tll_ptr ch_v22074, tll_env env) {
  tll_ptr call_ret_t344;
  call_ret_t344 = client_i40(ch_v22074);
  return call_ret_t344;
}

tll_ptr fork_fun_t349(tll_env env) {
  tll_ptr app_ret_t348; tll_ptr call_ret_t347; tll_ptr fork_ret_t351;
  call_ret_t347 = server_i39(env[0]);
  instr_app(&app_ret_t348, call_ret_t347, 0);
  instr_free_clo(call_ret_t347);
  fork_ret_t351 = app_ret_t348;
  instr_free_thread(env);
  return fork_ret_t351;
}

tll_ptr fork_fun_t356(tll_env env) {
  tll_ptr __v22082; tll_ptr app_ret_t355; tll_ptr c0_v22084;
  tll_ptr c_v22083; tll_ptr call_ret_t354; tll_ptr fork_ret_t358;
  tll_ptr recv_msg_t352; tll_ptr switch_ret_t353;
  instr_recv(&recv_msg_t352, env[0]);
  __v22082 = recv_msg_t352;
  switch(((tll_node)__v22082)->tag) {
    case 0:
      c_v22083 = ((tll_node)__v22082)->data[0];
      c0_v22084 = ((tll_node)__v22082)->data[1];
      instr_free_struct(__v22082);
      call_ret_t354 = client_i40(c_v22083);
      instr_app(&app_ret_t355, call_ret_t354, 0);
      instr_free_clo(call_ret_t354);
      switch_ret_t353 = app_ret_t355;
      break;
  }
  fork_ret_t358 = switch_ret_t353;
  instr_free_thread(env);
  return fork_ret_t358;
}

int main() {
  instr_init();
  tll_ptr Char_t196; tll_ptr Char_t199; tll_ptr Char_t202; tll_ptr Char_t205;
  tll_ptr Char_t208; tll_ptr Char_t211; tll_ptr Char_t214; tll_ptr Char_t217;
  tll_ptr Char_t220; tll_ptr Char_t223; tll_ptr EmptyString_t197;
  tll_ptr EmptyString_t200; tll_ptr EmptyString_t203;
  tll_ptr EmptyString_t206; tll_ptr EmptyString_t209;
  tll_ptr EmptyString_t212; tll_ptr EmptyString_t215;
  tll_ptr EmptyString_t218; tll_ptr EmptyString_t221;
  tll_ptr EmptyString_t224; tll_ptr String_t198; tll_ptr String_t201;
  tll_ptr String_t204; tll_ptr String_t207; tll_ptr String_t210;
  tll_ptr String_t213; tll_ptr String_t216; tll_ptr String_t219;
  tll_ptr String_t222; tll_ptr String_t225; tll_ptr __v22086;
  tll_ptr c0_v22077; tll_ptr c0_v22085; tll_ptr c_v22075;
  tll_ptr close_tmp_t360; tll_ptr consUU_t227; tll_ptr consUU_t228;
  tll_ptr consUU_t229; tll_ptr consUU_t230; tll_ptr consUU_t231;
  tll_ptr consUU_t232; tll_ptr consUU_t233; tll_ptr consUU_t234;
  tll_ptr consUU_t235; tll_ptr consUU_t236; tll_ptr fork_ch_t350;
  tll_ptr fork_ch_t357; tll_ptr lam_clo_t111; tll_ptr lam_clo_t12;
  tll_ptr lam_clo_t124; tll_ptr lam_clo_t137; tll_ptr lam_clo_t147;
  tll_ptr lam_clo_t157; tll_ptr lam_clo_t16; tll_ptr lam_clo_t167;
  tll_ptr lam_clo_t177; tll_ptr lam_clo_t186; tll_ptr lam_clo_t195;
  tll_ptr lam_clo_t22; tll_ptr lam_clo_t250; tll_ptr lam_clo_t255;
  tll_ptr lam_clo_t265; tll_ptr lam_clo_t273; tll_ptr lam_clo_t28;
  tll_ptr lam_clo_t281; tll_ptr lam_clo_t293; tll_ptr lam_clo_t318;
  tll_ptr lam_clo_t34; tll_ptr lam_clo_t346; tll_ptr lam_clo_t40;
  tll_ptr lam_clo_t46; tll_ptr lam_clo_t51; tll_ptr lam_clo_t57;
  tll_ptr lam_clo_t6; tll_ptr lam_clo_t66; tll_ptr lam_clo_t72;
  tll_ptr lam_clo_t78; tll_ptr lam_clo_t84; tll_ptr lam_clo_t92;
  tll_ptr lam_clo_t98; tll_ptr nilUU_t226; tll_ptr send_ch_t359;
  tll_ptr sleep_tmp_t361;
  instr_clo(&lam_clo_t6, &lam_fun_t5, 0);
  andbclo_i50 = lam_clo_t6;
  instr_clo(&lam_clo_t12, &lam_fun_t11, 0);
  orbclo_i51 = lam_clo_t12;
  instr_clo(&lam_clo_t16, &lam_fun_t15, 0);
  notbclo_i52 = lam_clo_t16;
  instr_clo(&lam_clo_t22, &lam_fun_t21, 0);
  ltenclo_i53 = lam_clo_t22;
  instr_clo(&lam_clo_t28, &lam_fun_t27, 0);
  gtenclo_i54 = lam_clo_t28;
  instr_clo(&lam_clo_t34, &lam_fun_t33, 0);
  ltnclo_i55 = lam_clo_t34;
  instr_clo(&lam_clo_t40, &lam_fun_t39, 0);
  gtnclo_i56 = lam_clo_t40;
  instr_clo(&lam_clo_t46, &lam_fun_t45, 0);
  eqnclo_i57 = lam_clo_t46;
  instr_clo(&lam_clo_t51, &lam_fun_t50, 0);
  predclo_i58 = lam_clo_t51;
  instr_clo(&lam_clo_t57, &lam_fun_t56, 0);
  addnclo_i59 = lam_clo_t57;
  instr_clo(&lam_clo_t66, &lam_fun_t65, 0);
  subnclo_i60 = lam_clo_t66;
  instr_clo(&lam_clo_t72, &lam_fun_t71, 0);
  mulnclo_i61 = lam_clo_t72;
  instr_clo(&lam_clo_t78, &lam_fun_t77, 0);
  divnclo_i62 = lam_clo_t78;
  instr_clo(&lam_clo_t84, &lam_fun_t83, 0);
  modnclo_i63 = lam_clo_t84;
  instr_clo(&lam_clo_t92, &lam_fun_t91, 0);
  catsclo_i64 = lam_clo_t92;
  instr_clo(&lam_clo_t98, &lam_fun_t97, 0);
  strlenclo_i65 = lam_clo_t98;
  instr_clo(&lam_clo_t111, &lam_fun_t110, 0);
  lenUUclo_i66 = lam_clo_t111;
  instr_clo(&lam_clo_t124, &lam_fun_t123, 0);
  lenULclo_i67 = lam_clo_t124;
  instr_clo(&lam_clo_t137, &lam_fun_t136, 0);
  lenLLclo_i68 = lam_clo_t137;
  instr_clo(&lam_clo_t147, &lam_fun_t146, 0);
  appendUUclo_i69 = lam_clo_t147;
  instr_clo(&lam_clo_t157, &lam_fun_t156, 0);
  appendULclo_i70 = lam_clo_t157;
  instr_clo(&lam_clo_t167, &lam_fun_t166, 0);
  appendLLclo_i71 = lam_clo_t167;
  instr_clo(&lam_clo_t177, &lam_fun_t176, 0);
  readlineclo_i72 = lam_clo_t177;
  instr_clo(&lam_clo_t186, &lam_fun_t185, 0);
  printclo_i73 = lam_clo_t186;
  instr_clo(&lam_clo_t195, &lam_fun_t194, 0);
  prerrclo_i74 = lam_clo_t195;
  instr_struct(&Char_t196, 1, 1, (tll_ptr)48);
  instr_struct(&EmptyString_t197, 2, 0);
  instr_struct(&String_t198, 3, 2, Char_t196, EmptyString_t197);
  instr_struct(&Char_t199, 1, 1, (tll_ptr)49);
  instr_struct(&EmptyString_t200, 2, 0);
  instr_struct(&String_t201, 3, 2, Char_t199, EmptyString_t200);
  instr_struct(&Char_t202, 1, 1, (tll_ptr)50);
  instr_struct(&EmptyString_t203, 2, 0);
  instr_struct(&String_t204, 3, 2, Char_t202, EmptyString_t203);
  instr_struct(&Char_t205, 1, 1, (tll_ptr)51);
  instr_struct(&EmptyString_t206, 2, 0);
  instr_struct(&String_t207, 3, 2, Char_t205, EmptyString_t206);
  instr_struct(&Char_t208, 1, 1, (tll_ptr)52);
  instr_struct(&EmptyString_t209, 2, 0);
  instr_struct(&String_t210, 3, 2, Char_t208, EmptyString_t209);
  instr_struct(&Char_t211, 1, 1, (tll_ptr)53);
  instr_struct(&EmptyString_t212, 2, 0);
  instr_struct(&String_t213, 3, 2, Char_t211, EmptyString_t212);
  instr_struct(&Char_t214, 1, 1, (tll_ptr)54);
  instr_struct(&EmptyString_t215, 2, 0);
  instr_struct(&String_t216, 3, 2, Char_t214, EmptyString_t215);
  instr_struct(&Char_t217, 1, 1, (tll_ptr)55);
  instr_struct(&EmptyString_t218, 2, 0);
  instr_struct(&String_t219, 3, 2, Char_t217, EmptyString_t218);
  instr_struct(&Char_t220, 1, 1, (tll_ptr)56);
  instr_struct(&EmptyString_t221, 2, 0);
  instr_struct(&String_t222, 3, 2, Char_t220, EmptyString_t221);
  instr_struct(&Char_t223, 1, 1, (tll_ptr)57);
  instr_struct(&EmptyString_t224, 2, 0);
  instr_struct(&String_t225, 3, 2, Char_t223, EmptyString_t224);
  instr_struct(&nilUU_t226, 12, 0);
  instr_struct(&consUU_t227, 13, 2, String_t225, nilUU_t226);
  instr_struct(&consUU_t228, 13, 2, String_t222, consUU_t227);
  instr_struct(&consUU_t229, 13, 2, String_t219, consUU_t228);
  instr_struct(&consUU_t230, 13, 2, String_t216, consUU_t229);
  instr_struct(&consUU_t231, 13, 2, String_t213, consUU_t230);
  instr_struct(&consUU_t232, 13, 2, String_t210, consUU_t231);
  instr_struct(&consUU_t233, 13, 2, String_t207, consUU_t232);
  instr_struct(&consUU_t234, 13, 2, String_t204, consUU_t233);
  instr_struct(&consUU_t235, 13, 2, String_t201, consUU_t234);
  instr_struct(&consUU_t236, 13, 2, String_t198, consUU_t235);
  digits_i28 = consUU_t236;
  instr_clo(&lam_clo_t250, &lam_fun_t249, 0);
  get_atclo_i75 = lam_clo_t250;
  instr_clo(&lam_clo_t255, &lam_fun_t254, 0);
  string_of_digitclo_i76 = lam_clo_t255;
  instr_clo(&lam_clo_t265, &lam_fun_t264, 0);
  string_of_natclo_i77 = lam_clo_t265;
  instr_clo(&lam_clo_t273, &lam_fun_t272, 0);
  gcdclo_i78 = lam_clo_t273;
  instr_clo(&lam_clo_t281, &lam_fun_t280, 0);
  lcmclo_i79 = lam_clo_t281;
  instr_clo(&lam_clo_t293, &lam_fun_t292, 0);
  powmclo_i80 = lam_clo_t293;
  instr_clo(&lam_clo_t318, &lam_fun_t317, 0);
  serverclo_i81 = lam_clo_t318;
  instr_clo(&lam_clo_t346, &lam_fun_t345, 0);
  clientclo_i82 = lam_clo_t346;
  instr_fork(&fork_ch_t350, &fork_fun_t349, 0);
  c_v22075 = fork_ch_t350;
  instr_fork(&fork_ch_t357, &fork_fun_t356, 0);
  c0_v22077 = fork_ch_t357;
  instr_send(&send_ch_t359, c0_v22077, c_v22075);
  c0_v22085 = send_ch_t359;
  instr_close(&close_tmp_t360, c0_v22085);
  __v22086 = close_tmp_t360;
  instr_sleep(&sleep_tmp_t361, (tll_ptr)1);
  return 0;
}

