/**
 * @file test_context_guard_unified.cpp
 * @brief Verify context guard RAII behavior for the dosbox context layer.
 */

#include <gtest/gtest.h>
#include <dosbox/dosbox_context.h>

using namespace dosbox;

TEST(ContextGuardUnified, DosboxGuardSetsAndRestoresContext) {
    EXPECT_FALSE(has_current_context());

    DOSBoxContext ctx{};
    {
        ContextGuard guard(ctx);
        EXPECT_TRUE(has_current_context());
        EXPECT_EQ(&current_context(), &ctx);
    }
    // Restored to null after guard destruction
    EXPECT_FALSE(has_current_context());
}

TEST(ContextGuardUnified, NestedGuardsRestoreCorrectly) {
    DOSBoxContext ctx1{};
    DOSBoxContext ctx2{};

    {
        ContextGuard guard1(ctx1);
        EXPECT_EQ(&current_context(), &ctx1);

        {
            ContextGuard guard2(ctx2);
            EXPECT_EQ(&current_context(), &ctx2);
        }
        // ctx1 restored after inner guard
        EXPECT_EQ(&current_context(), &ctx1);
    }
    EXPECT_FALSE(has_current_context());
}

TEST(ContextGuardUnified, TwoContextsAreIndependent) {
    DOSBoxContext ctx1{};
    DOSBoxContext ctx2{};

    ctx1.timing.total_cycles = 100;
    ctx2.timing.total_cycles = 200;

    {
        ContextGuard guard(ctx1);
        EXPECT_EQ(current_context().timing.total_cycles, 100u);
    }
    {
        ContextGuard guard(ctx2);
        EXPECT_EQ(current_context().timing.total_cycles, 200u);
    }
}
