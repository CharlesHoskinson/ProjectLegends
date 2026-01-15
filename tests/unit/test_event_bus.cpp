/**
 * @file test_event_bus.cpp
 * @brief Unit tests for InternalEventBus and ExternalEventBridge.
 */

#include <gtest/gtest.h>
#include <legends/event_bus.h>
#include <atomic>
#include <thread>
#include <vector>

using namespace legends;
using namespace legends::events;

// ─────────────────────────────────────────────────────────────────────────────
// EventSubscriptionToken Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(EventSubscriptionTokenTest, DefaultConstructorInvalid) {
    EventSubscriptionToken token;
    EXPECT_FALSE(token.valid());
}

TEST(EventSubscriptionTokenTest, MoveConstructor) {
    InternalEventBus bus;

    auto token1 = bus.subscribe([](const InternalEvent&) {});
    EXPECT_TRUE(token1.valid());
    uint32_t id = token1.id();

    EventSubscriptionToken token2(std::move(token1));

    EXPECT_FALSE(token1.valid());
    EXPECT_TRUE(token2.valid());
    EXPECT_EQ(token2.id(), id);
}

TEST(EventSubscriptionTokenTest, MoveAssignment) {
    InternalEventBus bus;

    auto token1 = bus.subscribe([](const InternalEvent&) {});
    auto token2 = bus.subscribe([](const InternalEvent&) {});

    EXPECT_EQ(bus.subscription_count(), 2u);

    token1 = std::move(token2);

    EXPECT_FALSE(token2.valid());
    EXPECT_TRUE(token1.valid());

    // Old token1 subscription should have been released
    EXPECT_EQ(bus.subscription_count(), 1u);
}

TEST(EventSubscriptionTokenTest, ExplicitRelease) {
    InternalEventBus bus;

    auto token = bus.subscribe([](const InternalEvent&) {});
    EXPECT_EQ(bus.subscription_count(), 1u);

    token.release();
    EXPECT_FALSE(token.valid());
    EXPECT_EQ(bus.subscription_count(), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// InternalEventBus Basic Tests
// ─────────────────────────────────────────────────────────────────────────────

class InternalEventBusTest : public ::testing::Test {
protected:
    InternalEventBus bus;
};

TEST_F(InternalEventBusTest, Subscribe) {
    int call_count = 0;

    auto token = bus.subscribe([&call_count](const InternalEvent&) {
        ++call_count;
    });

    EXPECT_TRUE(token.valid());
    EXPECT_EQ(bus.subscription_count(), 1u);
}

TEST_F(InternalEventBusTest, EmitTextScreen) {
    int call_count = 0;
    EventType received_type = EventType::Mouse;  // Set to something else

    auto token = bus.subscribe([&](const InternalEvent& event) {
        ++call_count;
        received_type = get_event_type(event);
    });

    TextModeScreen screen{};
    screen.columns = 80;
    screen.rows = 25;
    screen.timestamp_us = 12345;

    bus.emit(screen);

    EXPECT_EQ(call_count, 1);
    EXPECT_EQ(received_type, EventType::TextScreen);
}

TEST_F(InternalEventBusTest, EmitKeyboard) {
    EventType received_type = EventType::TextScreen;

    auto token = bus.subscribe([&](const InternalEvent& event) {
        received_type = get_event_type(event);
    });

    KeyboardEvent kbd{};
    kbd.scan_code = ScanCode::A;
    kbd.is_pressed = true;

    bus.emit(kbd);

    EXPECT_EQ(received_type, EventType::Keyboard);
}

TEST_F(InternalEventBusTest, EmitMouse) {
    EventType received_type = EventType::TextScreen;

    auto token = bus.subscribe([&](const InternalEvent& event) {
        received_type = get_event_type(event);
    });

    MouseEvent mouse{};
    mouse.delta_x = 10;
    mouse.delta_y = -5;
    mouse.buttons = MouseButtons::Left;

    bus.emit(mouse);

    EXPECT_EQ(received_type, EventType::Mouse);
}

TEST_F(InternalEventBusTest, EmitProgramStarted) {
    EventType received_type = EventType::TextScreen;

    auto token = bus.subscribe([&](const InternalEvent& event) {
        received_type = get_event_type(event);
    });

    ProgramStartedEvent started{};
    started.psp_segment = 0x1234;
    started.set_path("C:\\GAME.EXE");

    bus.emit(started);

    EXPECT_EQ(received_type, EventType::ProgramStarted);
}

TEST_F(InternalEventBusTest, EmitProgramHalted) {
    EventType received_type = EventType::TextScreen;

    auto token = bus.subscribe([&](const InternalEvent& event) {
        received_type = get_event_type(event);
    });

    ProgramHaltedEvent halted{};
    halted.reason = TerminationReason::NormalExit;
    halted.exit_code = 0;

    bus.emit(halted);

    EXPECT_EQ(received_type, EventType::ProgramHalted);
}

TEST_F(InternalEventBusTest, MultipleSubscribers) {
    int count1 = 0, count2 = 0, count3 = 0;

    auto token1 = bus.subscribe([&](const InternalEvent&) { ++count1; });
    auto token2 = bus.subscribe([&](const InternalEvent&) { ++count2; });
    auto token3 = bus.subscribe([&](const InternalEvent&) { ++count3; });

    EXPECT_EQ(bus.subscription_count(), 3u);

    KeyboardEvent kbd{};
    bus.emit(kbd);

    EXPECT_EQ(count1, 1);
    EXPECT_EQ(count2, 1);
    EXPECT_EQ(count3, 1);
}

TEST_F(InternalEventBusTest, UnsubscribeStopsDelivery) {
    int call_count = 0;

    auto token = bus.subscribe([&](const InternalEvent&) {
        ++call_count;
    });

    KeyboardEvent kbd{};

    bus.emit(kbd);
    EXPECT_EQ(call_count, 1);

    token.release();

    bus.emit(kbd);
    EXPECT_EQ(call_count, 1);  // No additional calls
}

TEST_F(InternalEventBusTest, TokenRAIIUnsubscribes) {
    int call_count = 0;

    {
        auto token = bus.subscribe([&](const InternalEvent&) {
            ++call_count;
        });
        EXPECT_EQ(bus.subscription_count(), 1u);
    }

    // Token went out of scope
    EXPECT_EQ(bus.subscription_count(), 0u);

    KeyboardEvent kbd{};
    bus.emit(kbd);

    EXPECT_EQ(call_count, 0);  // No calls after unsubscribe
}

TEST_F(InternalEventBusTest, ZeroCopySemantics) {
    const TextModeScreen* received_ptr = nullptr;

    auto token = bus.subscribe([&](const InternalEvent& event) {
        std::visit([&](auto&& e) {
            using T = std::decay_t<decltype(e.get())>;
            if constexpr (std::is_same_v<T, TextModeScreen>) {
                received_ptr = &e.get();
            }
        }, event);
    });

    TextModeScreen screen{};
    screen.columns = 80;

    bus.emit(screen);

    // Should receive pointer to same object (zero-copy)
    EXPECT_EQ(received_ptr, &screen);
}

// ─────────────────────────────────────────────────────────────────────────────
// InternalEventBus Threading Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST_F(InternalEventBusTest, ConcurrentEmit) {
    std::atomic<int> call_count{0};

    auto token = bus.subscribe([&](const InternalEvent&) {
        ++call_count;
    });

    std::vector<std::thread> threads;
    for (int i = 0; i < 4; ++i) {
        threads.emplace_back([&]() {
            for (int j = 0; j < 100; ++j) {
                KeyboardEvent kbd{};
                bus.emit(kbd);
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    EXPECT_EQ(call_count.load(), 400);
}

TEST_F(InternalEventBusTest, ConcurrentSubscribeUnsubscribe) {
    std::atomic<int> active_subs{0};
    std::vector<std::thread> threads;

    for (int i = 0; i < 4; ++i) {
        threads.emplace_back([&]() {
            for (int j = 0; j < 50; ++j) {
                auto token = bus.subscribe([](const InternalEvent&) {});
                active_subs++;
                std::this_thread::yield();
                token.release();
                active_subs--;
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    EXPECT_EQ(bus.subscription_count(), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// ExternalEventBridge Tests
// ─────────────────────────────────────────────────────────────────────────────

class ExternalEventBridgeTest : public ::testing::Test {
protected:
    InternalEventBus internal_bus;
};

TEST_F(ExternalEventBridgeTest, Construction) {
    ExternalEventBridge bridge(internal_bus);

    EXPECT_EQ(bridge.pending_count(), 0u);
    EXPECT_EQ(bridge.subscription_count(), 0u);
}

TEST_F(ExternalEventBridgeTest, Subscribe) {
    ExternalEventBridge bridge(internal_bus);

    int call_count = 0;
    auto callback = [](int type, const void* data, size_t size, void* user) {
        int* count = static_cast<int*>(user);
        (*count)++;
    };

    bridge.subscribe(EventType::Keyboard, callback, &call_count);

    EXPECT_EQ(bridge.subscription_count(), 1u);
}

TEST_F(ExternalEventBridgeTest, EventQueued) {
    ExternalEventBridge bridge(internal_bus);

    int call_count = 0;
    auto callback = [](int type, const void* data, size_t size, void* user) {
        int* count = static_cast<int*>(user);
        (*count)++;
    };

    bridge.subscribe(EventType::Keyboard, callback, &call_count);

    // Emit event to internal bus (should be queued in bridge)
    KeyboardEvent kbd{};
    internal_bus.emit(kbd);

    EXPECT_EQ(bridge.pending_count(), 1u);
    EXPECT_EQ(call_count, 0);  // Not delivered yet
}

TEST_F(ExternalEventBridgeTest, FlushDelivers) {
    ExternalEventBridge bridge(internal_bus);

    int call_count = 0;
    auto callback = [](int type, const void* data, size_t size, void* user) {
        int* count = static_cast<int*>(user);
        (*count)++;
    };

    bridge.subscribe(EventType::Keyboard, callback, &call_count);

    KeyboardEvent kbd{};
    internal_bus.emit(kbd);

    size_t flushed = bridge.flush();

    EXPECT_EQ(flushed, 1u);
    EXPECT_EQ(call_count, 1);
    EXPECT_EQ(bridge.pending_count(), 0u);
}

TEST_F(ExternalEventBridgeTest, FilterByEventType) {
    ExternalEventBridge bridge(internal_bus);

    int kbd_count = 0, mouse_count = 0;

    bridge.subscribe(EventType::Keyboard,
        [](int, const void*, size_t, void* user) {
            (*static_cast<int*>(user))++;
        }, &kbd_count);

    bridge.subscribe(EventType::Mouse,
        [](int, const void*, size_t, void* user) {
            (*static_cast<int*>(user))++;
        }, &mouse_count);

    KeyboardEvent kbd{};
    MouseEvent mouse{};

    internal_bus.emit(kbd);
    internal_bus.emit(mouse);

    bridge.flush();

    EXPECT_EQ(kbd_count, 1);
    EXPECT_EQ(mouse_count, 1);
}

TEST_F(ExternalEventBridgeTest, Unsubscribe) {
    ExternalEventBridge bridge(internal_bus);

    int call_count = 0;
    auto callback = [](int type, const void* data, size_t size, void* user) {
        int* count = static_cast<int*>(user);
        (*count)++;
    };

    bridge.subscribe(EventType::Keyboard, callback, &call_count);
    bridge.unsubscribe(EventType::Keyboard, callback);

    KeyboardEvent kbd{};
    internal_bus.emit(kbd);
    bridge.flush();

    EXPECT_EQ(call_count, 0);  // Unsubscribed, shouldn't be called
}

TEST_F(ExternalEventBridgeTest, TextDiffModeToggle) {
    ExternalEventBridge bridge(internal_bus);

    EXPECT_FALSE(bridge.text_diff_enabled());

    bridge.set_text_diff_mode(true);
    EXPECT_TRUE(bridge.text_diff_enabled());

    bridge.set_text_diff_mode(false);
    EXPECT_FALSE(bridge.text_diff_enabled());
}

TEST_F(ExternalEventBridgeTest, MultipleEvents) {
    ExternalEventBridge bridge(internal_bus);

    int call_count = 0;
    auto callback = [](int type, const void*, size_t, void* user) {
        (*static_cast<int*>(user))++;
    };

    bridge.subscribe(EventType::Keyboard, callback, &call_count);

    for (int i = 0; i < 10; ++i) {
        KeyboardEvent kbd{};
        internal_bus.emit(kbd);
    }

    EXPECT_EQ(bridge.pending_count(), 10u);

    bridge.flush();

    EXPECT_EQ(call_count, 10);
    EXPECT_EQ(bridge.pending_count(), 0u);
}

// ─────────────────────────────────────────────────────────────────────────────
// get_event_type Tests
// ─────────────────────────────────────────────────────────────────────────────

TEST(GetEventTypeTest, AllEventTypes) {
    {
        TextModeScreen screen{};
        InternalEvent event{std::cref(screen)};
        EXPECT_EQ(get_event_type(event), EventType::TextScreen);
    }
    {
        TextModeDiff diff{};
        InternalEvent event{std::cref(diff)};
        EXPECT_EQ(get_event_type(event), EventType::TextDiff);
    }
    {
        ProgramStartedEvent started{};
        InternalEvent event{std::cref(started)};
        EXPECT_EQ(get_event_type(event), EventType::ProgramStarted);
    }
    {
        ProgramHaltedEvent halted{};
        InternalEvent event{std::cref(halted)};
        EXPECT_EQ(get_event_type(event), EventType::ProgramHalted);
    }
    {
        KeyboardEvent kbd{};
        InternalEvent event{std::cref(kbd)};
        EXPECT_EQ(get_event_type(event), EventType::Keyboard);
    }
    {
        MouseEvent mouse{};
        InternalEvent event{std::cref(mouse)};
        EXPECT_EQ(get_event_type(event), EventType::Mouse);
    }
}
