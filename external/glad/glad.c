// SPDX-License-Identifier: GPL-2.0-or-later
// Copyright (C) 2024-2025 Charles Hoskinson and Contributors
//
// glad.c — Stub implementation of the glad GL loader.
// The real loader is generated from https://glad.dav1d.de/ and vendored.
// This stub defines all function pointers as NULL and provides a no-op loader.

#include "glad/glad.h"
#include <stddef.h>

// ---------------------------------------------------------------------------
// Function pointer definitions (all NULL — populated by gladLoadGLLoader)
// ---------------------------------------------------------------------------
GLuint  (*glCreateShader)(GLenum type) = NULL;
void    (*glShaderSource)(GLuint shader, GLsizei count,
                          const GLchar *const* string,
                          const GLint *length) = NULL;
void    (*glCompileShader)(GLuint shader) = NULL;
void    (*glGetShaderiv)(GLuint shader, GLenum pname, GLint *params) = NULL;
void    (*glGetShaderInfoLog)(GLuint shader, GLsizei bufSize,
                              GLsizei *length, GLchar *infoLog) = NULL;
GLuint  (*glCreateProgram)(void) = NULL;
void    (*glAttachShader)(GLuint program, GLuint shader) = NULL;
void    (*glLinkProgram)(GLuint program) = NULL;
void    (*glGetProgramiv)(GLuint program, GLenum pname, GLint *params) = NULL;
void    (*glGetProgramInfoLog)(GLuint program, GLsizei bufSize,
                               GLsizei *length, GLchar *infoLog) = NULL;
void    (*glDeleteShader)(GLuint shader) = NULL;
void    (*glDeleteProgram)(GLuint program) = NULL;
void    (*glUseProgram)(GLuint program) = NULL;

void    (*glGenVertexArrays)(GLsizei n, GLuint *arrays) = NULL;
void    (*glBindVertexArray)(GLuint array) = NULL;
void    (*glDeleteVertexArrays)(GLsizei n, const GLuint *arrays) = NULL;

void    (*glGenBuffers)(GLsizei n, GLuint *buffers) = NULL;
void    (*glBindBuffer)(GLenum target, GLuint buffer) = NULL;
void    (*glBufferData)(GLenum target, GLsizeiptr size,
                        const void *data, GLenum usage) = NULL;
void    (*glDeleteBuffers)(GLsizei n, const GLuint *buffers) = NULL;

void    (*glVertexAttribPointer)(GLuint index, GLint size, GLenum type,
                                 GLboolean normalized, GLsizei stride,
                                 const void *pointer) = NULL;
void    (*glEnableVertexAttribArray)(GLuint index) = NULL;

void    (*glDrawArrays)(GLenum mode, GLint first, GLsizei count) = NULL;

void    (*glGenFramebuffers)(GLsizei n, GLuint *framebuffers) = NULL;
void    (*glBindFramebuffer)(GLenum target, GLuint framebuffer) = NULL;
void    (*glFramebufferTexture2D)(GLenum target, GLenum attachment,
                                  GLenum textarget, GLuint texture,
                                  GLint level) = NULL;
void    (*glDeleteFramebuffers)(GLsizei n,
                                const GLuint *framebuffers) = NULL;

void    (*glGenTextures)(GLsizei n, GLuint *textures) = NULL;
void    (*glBindTexture)(GLenum target, GLuint texture) = NULL;
void    (*glTexImage2D)(GLenum target, GLint level, GLint internalformat,
                        GLsizei width, GLsizei height, GLint border,
                        GLenum format, GLenum type,
                        const void *pixels) = NULL;
void    (*glTexParameteri)(GLenum target, GLenum pname, GLint param) = NULL;
void    (*glDeleteTextures)(GLsizei n, const GLuint *textures) = NULL;

GLint   (*glGetUniformLocation)(GLuint program, const GLchar *name) = NULL;
void    (*glUniform1i)(GLint location, GLint v0) = NULL;
void    (*glUniform1f)(GLint location, GLfloat v0) = NULL;
void    (*glUniform2f)(GLint location, GLfloat v0, GLfloat v1) = NULL;

void    (*glViewport)(GLint x, GLint y, GLsizei width, GLsizei height) = NULL;
void    (*glClear)(GLbitfield mask) = NULL;
void    (*glClearColor)(GLfloat red, GLfloat green, GLfloat blue,
                        GLfloat alpha) = NULL;

void    (*glActiveTexture)(GLenum texture) = NULL;
GLenum  (*glCheckFramebufferStatus)(GLenum target) = NULL;

// ---------------------------------------------------------------------------
// Stub loader — in production this resolves function pointers via the
// platform's GL loader (e.g. SDL_GL_GetProcAddress).
// ---------------------------------------------------------------------------
int gladLoadGLLoader(void* (*load)(const char *name)) {
    (void)load;
    return 1; // success stub
}
